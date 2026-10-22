import CA.Registry.Basic
import CA.Canonical
import CA.SHA256
import CA.ExprHash
import CA.RefHash
import CA.Util
import Lean.Util.Path

/-!
# Registry Generation Command

Provides `#ca_registry "output_dir/"` — a command that generates
`declarations.json` and `meta.json` from `@[publish]` and `@[open_point]`
annotated declarations in the current environment.

Intended to be placed at the end of a project's registry file so that
`lake build` automatically produces the registry as a side-effect. Files
are rewritten only when their content changes, so re-elaboration (e.g. in
an editor) leaves a committed registry untouched.

The heavy lifting lives in `generateRegistryCore`, which is plain `IO`
over an `Environment` so that the `ca registry` CLI subcommand can reuse
it — both paths must produce byte-identical registries, or "addresses are
computed, not assigned" would be false. Hashing goes through a
`CA.SHA256.Hasher` (pure Lean by default; the CLI passes OpenSSL).

## The two-tier key

Every entry carries two statement ids:

* `stmt` — the exact `RefHash` statement id (base58): references are
  embedded by *their* ids, so it is exact with respect to the whole cone
  down to Lean's core, and changes whenever anything in that cone does.
  `ref` is the declaration's `RefHash.ref` (what a dependent embeds:
  `stmt` for theorems, the value-inclusive `decl` otherwise).
* `type_hash` — the coarse name-based L0 hash (hex): references by name,
  so stable across toolchain releases and blind to redefinitions.

Two registries match exactly on `stmt`, or coarsely on `type_hash`.
For an `@[open_point]` `def P : Prop := S` both ids are of the
*statement* `S`, so a theorem `: S` matches `P` on both tiers.

Computing `stmt` needs the `ref` of every constant the statements
mention, transitively, down to core: the **statement cone**
(`statementCone`), which follows type references always and value /
structural references of non-theorems, never theorem proofs
(`RefHash.computeIds (withProofs := false)`). The `ref`s of the
*imported* part of the cone are cached under `.lake/ca/`, keyed by the
Lean version, the encoding scheme and the identity of every imported
`.olean`, so a rebuild recomputes only the project's own declarations.

## Status classification

One entry per annotated name (a name carrying both attributes is one open
point). Statuses:

| status        | who                                                        |
|---------------|------------------------------------------------------------|
| `open`        | an `@[open_point]` no published theorem proves             |
| `proved`      | a theorem whose hypotheses mention no still-open point, or an open point some published theorem proves |
| `conditional` | a theorem with a hypothesis that reaches a still-open point |
| `definition`  | any published non-theorem, non-axiom                       |
| `axiom`       | a published axiom (an assumption, never "proved")          |

A published theorem **proves** an open point `o` when its type is the
constant `o`, or when its type's address equals `o`'s statement address
(`o` is `def o : Prop := S`; a theorem `: S` proves it). Such a theorem is
`proved` and lists `o` in `proves`; `o` lists it in `proved_by`.

A theorem's **hypotheses** are the binder domains of its type's top-level
`∀`-telescope. A hypothesis *reaches* an open point if it mentions one,
directly or through the values of Prop-valued definitions
(`def Wrap : Prop := Conj ∧ True`). The open points reached are recorded
in `status_deps`; the theorem is `conditional` while any of them is
still open and `proved` once all of them have proofs in this registry
(the cascade of `registry-design.md`, within one registry). Open points
in the *conclusion* do not make a theorem conditional: `¬ Conj` or
`Conj ∧ True` are theorems about the statement, not uses of it.
-/

open Lean Elab Command
open CA.Registry CA.ExprHash CA.Canonical CA.SHA256 CA.Util

namespace CA.Registry

/-- Status of a registry entry (see the module docstring). -/
inductive Status where
  | «open» | proved | conditional | definition | «axiom»
  deriving BEq, Repr, Inhabited

def Status.toString : Status → String
  | .«open» => "open"
  | .proved => "proved"
  | .conditional => "conditional"
  | .definition => "definition"
  | .«axiom» => "axiom"

instance : ToString Status := ⟨Status.toString⟩

/-- The expression a registry entry is addressed by: for a `def _ : Prop`
    (an open point, or any published proposition) the *statement* is the
    definition's value; for everything else it is the type. -/
def hashTarget (ci : ConstantInfo) : Expr :=
  match ci with
  | .defnInfo d => if ci.type.isProp then d.value else ci.type
  | _ => ci.type

/-- The registry address of an expression: the name-based L0 hash, hex. -/
def exprAddress (e : Expr) : String :=
  toHex256 (sha256Pure (serializeExpr (canonicalizeL0 e)))

/-- Binder domains of the top-level `∀`-telescope of a type: its
    hypotheses. (Bodies keep their loose bvars; only constants are read.) -/
partial def hypothesesOf : Expr → Array Expr → Array Expr
  | .forallE _ dom body _, acc => hypothesesOf body (acc.push dom)
  | .mdata _ e, acc => hypothesesOf e acc
  | _, acc => acc

private def sortNames (ns : Array Name) : Array Name := ns.qsort Name.lt

/-- Open points reachable from constant `n`: `n` itself if it is one;
    otherwise, when `n` is a Prop-valued definition, those reachable from
    the constants of its value. Memoised; a cycle contributes nothing. -/
partial def openPointsReached (env : Environment) (openSet : NameSet) (n : Name)
    (memo : Std.HashMap Name (Array Name)) : Array Name × Std.HashMap Name (Array Name) :=
  if openSet.contains n then (#[n], memo)
  else match memo.get? n with
  | some r => (r, memo)
  | none =>
    let memo := memo.insert n #[]   -- in progress: cycle guard
    match env.find? n with
    | some (.defnInfo d) =>
      if d.type.isProp then
        let (acc, memo) := (collectConstants d.value).toArray.foldl
          (fun (acc, memo) c =>
            let (r, memo) := openPointsReached env openSet c memo
            (r.foldl (·.insert ·) acc, memo))
          (({} : NameSet), memo)
        let res := acc.toArray
        (res, memo.insert n res)
      else (#[], memo)
    | _ => (#[], memo)

/-! ## Exact ids: statement cone, cached base table -/

/-- Exact (`RefHash`) ids of a registry entry. -/
structure EntryIds where
  /-- Statement id; for an `@[open_point]` the id of its *statement* (the
      definition's value), so a theorem proving it has the same `stmt`. -/
  stmt       : ByteArray
  /-- What a dependent embeds: `stmt` for theorems, `decl` otherwise. -/
  ref        : ByteArray
  /-- Constants that had to be hashed by name (empty means exact). -/
  unresolved : Array Name := #[]
  deriving Inhabited

/-- The constants whose `ref` ids the exact ids of `roots` need: the
    closure of `roots` under type references and under value / structural
    references of non-theorems. Theorem proofs are never followed
    (`ref(theorem) = stmt`), which keeps the cone a small fraction of the
    environment. -/
def statementCone (env : Environment) (roots : Array Name) : Array (Name × ConstantInfo) := Id.run do
  let mut seen : NameSet := {}
  let mut out : Array (Name × ConstantInfo) := #[]
  let mut stack : Array Name := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    out := out.push (n, ci)
    for m in (RefHash.refsOf ci (withProofs := false)).toArray do
      if !seen.contains m then stack := stack.push m
  return out

/-- Key under which the `ref` table of the *imported* part of a cone is
    cached: Lean version, encoding scheme, and path / size / mtime of
    every imported `.olean`. Any change to the imports changes the key. -/
def importsCacheKey (env : Environment) : IO String := do
  let mut parts : Array String := #[s!"lean={Lean.versionString}", s!"scheme={CA.schemeVersion}"]
  for m in env.header.moduleNames do
    let stamp ← try
        let p ← findOLean m
        let md ← p.metadata
        pure s!"{p}|{md.byteSize}|{md.modified.sec}.{md.modified.nsec}"
      catch _ => pure "?"
    parts := parts.push s!"{m}|{stamp}"
  return toHex256 (sha256Pure (String.intercalate "\n" parts.toList).toUTF8)

/-! Binary `RefTable` cache: `magic ‖ count ‖ (name ‖ 0x03 ‖ len ‖ ref)*`,
    names component-wise (`0x00` root, `0x01 len utf8` / `0x02 u64` per
    component), little-endian u64 lengths. A malformed file is ignored. -/

private def cacheMagic : ByteArray := "CA-reftable-1\n".toUTF8

private def putU64 (b : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut b := b
  let mut v := n.toUInt64
  for _ in [:8] do
    b := b.push (v &&& 0xFF).toUInt8
    v := v >>> 8
  return b

private def putBytes (b bs : ByteArray) : ByteArray := (putU64 b bs.size) ++ bs

private partial def putName (b : ByteArray) : Name → ByteArray
  | .anonymous => b.push 0
  | .str p s   => putBytes ((putName b p).push 1) s.toUTF8
  | .num p n   => putU64 ((putName b p).push 2) n

private abbrev Rd := StateT Nat (Except Unit)

private def rdU8 (b : ByteArray) : Rd UInt8 := do
  let i ← get
  if i < b.size then set (i + 1); return b.get! i else throw ()

private def rdU64 (b : ByteArray) : Rd Nat := do
  let mut v : Nat := 0
  for k in [:8] do
    let x ← rdU8 b
    v := v + (x.toNat <<< (8 * k))
  return v

private def rdBytes (b : ByteArray) : Rd ByteArray := do
  let n ← rdU64 b
  let i ← get
  if i + n ≤ b.size then set (i + n); return b.extract i (i + n) else throw ()

private partial def rdNameLoop (b : ByteArray) (acc : Name) : Rd Name := do
  match ← rdU8 b with
  | 1 => let s ← rdBytes b; rdNameLoop b (.str acc (String.fromUTF8! s))
  | 2 => let n ← rdU64 b; rdNameLoop b (.num acc n)
  | 3 => return acc
  | _ => throw ()

private def rdName (b : ByteArray) : Rd Name := do
  if (← rdU8 b) != 0 then throw ()
  rdNameLoop b .anonymous

/-- Write a `RefTable` cache file (entries sorted by name). -/
def writeRefTable (path : System.FilePath) (t : RefHash.RefTable) : IO Unit := do
  let entries := t.toArray.qsort fun a b => Name.lt a.1 b.1
  let mut b := cacheMagic
  b := putU64 b entries.size
  for (n, r) in entries do
    b := (putName b n).push 3
    b := putBytes b r
  if let some d := path.parent then IO.FS.createDirAll d
  IO.FS.writeBinFile path b

/-- Read a `RefTable` cache file; `none` if absent or malformed. -/
def readRefTable (path : System.FilePath) : IO (Option RefHash.RefTable) := do
  unless ← path.pathExists do return none
  let b ← IO.FS.readBinFile path
  if b.size < cacheMagic.size || b.extract 0 cacheMagic.size != cacheMagic then return none
  let parse : Rd RefHash.RefTable := do
    let n ← rdU64 b
    let mut t : RefHash.RefTable := {}
    for _ in [:n] do
      let name ← rdName b
      let r ← rdBytes b
      if r.size != 32 then throw ()
      t := t.insert name r
    return t
  match parse.run cacheMagic.size with
  | .ok (t, _) => return some t
  | .error _ => return none

/-- Default cache directory, relative to the working directory (the
    project root under `lake build`). -/
def defaultCacheDir : System.FilePath := ".lake" / "ca"

/-- Exact ids for `roots`: compute the statement cone, load the cached
    `ref` table for the imports (if `cacheDir`), compute what is missing
    plus the roots themselves (`withProofs := false`), extend the cache
    with the exact imported results, and return each root's `stmt` /
    `ref`. For an `@[open_point]` (`def _ : Prop`) `stmt` is the id of
    its statement, i.e. the value. -/
def computeEntryIds (env : Environment) (roots : Array Name) (hasher : Hasher := pureHasher)
    (cacheDir : Option System.FilePath := some defaultCacheDir) : IO (Std.HashMap Name EntryIds) := do
  let cone := statementCone env roots
  let cachePath ← match cacheDir with
    | some d => pure (some (d / s!"reftable-{← importsCacheKey env}.bin"))
    | none => pure none
  let base : RefHash.RefTable ← match cachePath with
    | some p => pure ((← readRefTable p).getD {})
    | none => pure {}
  let rootSet : NameSet := roots.foldl (·.insert ·) {}
  let todo := cone.filter fun (n, _) => rootSet.contains n || !base.contains n
  let (ids, table) ← RefHash.computeIds todo base hasher (withProofs := false)
  if let some p := cachePath then
    let mut cache := base
    for d in ids do
      if d.unresolved.isEmpty && (env.getModuleIdxFor? d.name).isSome then
        cache := cache.insert d.name d.ref
    if cache.size > base.size then
      try writeRefTable p cache catch _ => pure ()
  let byName : Std.HashMap Name RefHash.DeclIds := ids.foldl (fun m d => m.insert d.name d) {}
  let mut out : Std.HashMap Name EntryIds := {}
  for n in roots do
    let some d := byName.get? n | continue
    let some ci := env.find? n | continue
    let (stmt, unres) ← match ci with
      | .defnInfo v =>
        if ci.type.isProp then RefHash.stmtIdOf v.levelParams v.value table hasher
        else pure (d.stmt, #[])
      | _ => pure (d.stmt, #[])
    let unresolved := ((unres ++ d.unresolved).foldl (fun (s : NameSet) x => s.insert x) {}).toArray
    out := out.insert n { stmt, ref := d.ref, unresolved }
  return out

/-! ## Classification -/

/-- The annotated names of `env`, sorted, one per name: `(name, isOpenPoint,
    description)`. An open point wins over `@[publish]` on the same name;
    the publish description is the fallback. -/
def annotated (env : Environment) : Array (Name × Bool × String) := Id.run do
  let openPoints := getOpenPoints env
  let published := getPublished env
  let openSet : NameSet := openPoints.foldl (fun s (n, _) => s.insert n) {}
  let mut descs : NameMap String := {}
  for (n, e) in published do descs := descs.insert n e.description
  for (n, e) in openPoints do
    let d := if e.description.isEmpty then (descs.find? n).getD "" else e.description
    descs := descs.insert n d
  let names := sortNames (descs.toList.map (·.1)).toArray
  return names.map fun n => (n, openSet.contains n, (descs.find? n).getD "")

/-- One classified registry entry. -/
structure Entry where
  name        : Name
  ci          : ConstantInfo
  isOpenPoint : Bool
  description : String
  /-- Coarse tier: name-based L0 hash of the statement, hex. -/
  address     : String
  /-- Exact tier: `RefHash` statement id. -/
  stmt        : ByteArray
  /-- `RefHash.ref`: what a dependent embeds. -/
  ref         : ByteArray
  /-- Names hashed by name while computing the exact ids (empty = exact). -/
  unresolved  : Array Name
  status      : Status
  /-- Theorems: open points this theorem proves. -/
  proves      : Array Name := #[]
  /-- Open points: published theorems that prove them. -/
  provedBy    : Array Name := #[]
  /-- Theorems: open points reached from the hypotheses. -/
  statusDeps  : Array Name := #[]

/-- Classify every annotated declaration of `env`, given their exact ids
    (`computeEntryIds env (annotated env |>.map (·.1))`). Sorted by name;
    one entry per name. -/
def classify (env : Environment) (ids : Std.HashMap Name EntryIds) : Array Entry := Id.run do
  let ann := annotated env
  let openSet : NameSet := ann.foldl (fun s (n, isOpen, _) => if isOpen then s.insert n else s) {}
  -- Pass 1: ids; open points by exact statement id.
  let mut base : Array Entry := #[]
  let mut openByStmt : Std.HashMap String (Array Name) := {}
  for (n, isOpen, desc) in ann do
    let some ci := env.find? n | continue
    let eid := ids.getD n default
    let key := RefHash.toB58 eid.stmt
    if isOpen then openByStmt := openByStmt.insert key ((openByStmt.getD key #[]).push n)
    base := base.push { name := n, ci, isOpenPoint := isOpen, description := desc,
                        address := exprAddress (hashTarget ci), stmt := eid.stmt, ref := eid.ref,
                        unresolved := eid.unresolved, status := .definition }
  -- Pass 2: which open points are proved by a published theorem — by the
  -- open point's constant, or by equal exact statement id (a theorem
  -- stating the proposition literally).
  let provesOf (e : Entry) : Array Name :=
    if e.isOpenPoint then #[] else
    match e.ci with
    | .thmInfo _ =>
      let byConst : Array Name := match stripMData e.ci.type with
        | .const c _ => if openSet.contains c then #[c] else #[]
        | _ => #[]
      let byStmt := openByStmt.getD (RefHash.toB58 e.stmt) #[]
      sortNames (byStmt.foldl (fun (s : NameSet) x => s.insert x) (byConst.foldl (·.insert ·) {})).toArray
    | _ => #[]
  let mut provedBy : NameMap (Array Name) := {}
  let mut proves : NameMap (Array Name) := {}
  for e in base do
    let ps := provesOf e
    if !ps.isEmpty then
      proves := proves.insert e.name ps
      for o in ps do provedBy := provedBy.insert o ((provedBy.find? o |>.getD #[]).push e.name)
  -- Pass 3: statuses.
  let mut memo : Std.HashMap Name (Array Name) := {}
  let mut out : Array Entry := #[]
  for e in base do
    if e.isOpenPoint then
      let pb := provedBy.find? e.name |>.getD #[]
      out := out.push { e with status := if pb.isEmpty then .«open» else .proved, provedBy := pb }
    else match e.ci with
    | .thmInfo _ =>
      if let some ps := proves.find? e.name then
        out := out.push { e with status := .proved, proves := ps }
      else
        let mut deps : NameSet := {}
        for h in hypothesesOf e.ci.type #[] do
          for c in (collectConstants h).toArray do
            let (r, memo') := openPointsReached env openSet c memo
            memo := memo'
            deps := r.foldl (·.insert ·) deps
        let depsArr := deps.toArray
        let stillOpen := depsArr.any fun o => (provedBy.find? o |>.getD #[]).isEmpty
        out := out.push { e with status := if stillOpen then .conditional else .proved, statusDeps := depsArr }
    | .axiomInfo _ => out := out.push { e with status := .«axiom» }
    | _ => out := out.push { e with status := .definition }
  return out

/-- JSON for one entry (`pp_type` needs `MetaM`). -/
private def entryToJson (env : Environment) (e : Entry) : IO Lean.Json := do
  let target := hashTarget e.ci
  let ppType ← runMetaM env do return (← Meta.ppExpr target).pretty
  let names (ns : Array Name) : Lean.Json := .arr (ns.map (.str ·.toString))
  let mut fields : List (String × Lean.Json) := [
    ("name", .str e.name.toString),
    ("module", .str (getModuleName env e.name).toString),
    ("kind", .str (constantKind e.ci)),
    ("status", .str e.status.toString),
    ("type_hash", .str e.address),
    ("stmt", .str (RefHash.toB58 e.stmt)),
    ("ref", .str (RefHash.toB58 e.ref)),
    ("pp_type", .str ppType),
    ("type_deps", names (collectConstants target).toArray)
  ]
  if !e.unresolved.isEmpty then fields := fields ++ [("unresolved", names e.unresolved)]
  if !e.description.isEmpty then fields := fields ++ [("description", .str e.description)]
  if !e.proves.isEmpty then fields := fields ++ [("proves", names e.proves)]
  if !e.provedBy.isEmpty then fields := fields ++ [("proved_by", names e.provedBy)]
  if !e.statusDeps.isEmpty then fields := fields ++ [("status_deps", names e.statusDeps)]
  return .mkObj fields

/-- Per-run summary of a registry generation. -/
structure RegistrySummary where
  entries     : Nat
  /-- Entries annotated `@[open_point]`. -/
  openPoints  : Nat
  /-- Of those, proved by a published theorem in this registry. -/
  openProved  : Nat
  /-- Entries that are not open points. -/
  published   : Nat
  proved      : Nat
  conditional : Nat
  definitions : Nat
  axioms      : Nat
  declsPath   : String
  metaPath    : String
  /-- Whether any file was (re)written. -/
  changed     : Bool

/-- Write `content` to `path` unless the file already has exactly that
    content. Returns whether it wrote. -/
private def writeIfChanged (path : String) (content : String) : IO Bool := do
  let same ← try pure ((← IO.FS.readFile path) == content) catch _ => pure false
  unless same do IO.FS.writeFile path content
  return !same

/-- Generate `declarations.json` and `meta.json` from the `@[publish]` /
    `@[open_point]` annotations in `env`. Plain `IO`, shared by the
    `#ca_registry` command and the `ca registry` CLI subcommand.
    `toolchain` (when known) is recorded in `meta.json`. -/
def generateRegistryCore (env : Environment) (outputDir : String)
    (project : String := "registry") (toolchain : Option String := none)
    (hasher : Hasher := pureHasher) (cacheDir : Option System.FilePath := some defaultCacheDir)
    : IO RegistrySummary := do
  let ids ← computeEntryIds env ((annotated env).map (·.1)) hasher cacheDir
  let entries := classify env ids
  let mut json : Array Lean.Json := #[]
  for e in entries do json := json.push (← entryToJson env e)

  let count (p : Entry → Bool) : Nat := entries.foldl (fun n e => if p e then n + 1 else n) 0
  let openPoints  := count (·.isOpenPoint)
  let openProved  := count fun e => e.isOpenPoint && e.status == .proved
  let published   := entries.size - openPoints
  let proved      := count fun e => !e.isOpenPoint && e.status == .proved
  let conditional := count (·.status == .conditional)
  let definitions := count (·.status == .definition)
  let axioms      := count (·.status == .«axiom»)

  IO.FS.createDirAll outputDir
  let declsPath := s!"{outputDir}/declarations.json"
  let c1 ← writeIfChanged declsPath (Lean.Json.arr json).pretty

  let num (n : Nat) : Lean.Json := .num ⟨n, 0⟩
  let mut metaFields : List (String × Lean.Json) := [
    ("project", .str project),
    ("ca_hash_level", .str "L0"),
    ("ca_hash_mode", .str "name-based"),
    ("ca_scheme_version", num CA.schemeVersion),
    ("ca_key_tiers", .mkObj [
      ("exact", .str "stmt (RefHash statement id, base58); ref = what dependents embed"),
      ("coarse", .str "type_hash (name-based L0 SHA-256, hex)")]),
    ("entries", num entries.size),
    ("open_points", num openPoints),
    ("open_points_proved", num openProved),
    ("published", num published),
    ("proved", num proved),
    ("conditional", num conditional),
    ("definitions", num definitions),
    ("axioms", num axioms)
  ]
  if let some tc := toolchain then
    metaFields := metaFields ++ [("lean_toolchain", .str tc)]
  let metaPath := s!"{outputDir}/meta.json"
  let c2 ← writeIfChanged metaPath (Lean.Json.mkObj metaFields).pretty

  return { entries := entries.size, openPoints, openProved, published, proved, conditional,
           definitions, axioms, declsPath, metaPath, changed := c1 || c2 }

/-- Generate registry files from the current environment.
    Writes `declarations.json` and `meta.json` to the given output directory. -/
def generateRegistryFiles (outputDir : String) : CommandElabM Unit := do
  let env ← getEnv
  let toolchain ← try
      pure (some (← IO.FS.readFile "lean-toolchain").trimAscii.toString)
    catch _ => pure none
  let project := if env.mainModule == .anonymous then "registry"
    else env.mainModule.toString
  let s ← generateRegistryCore env outputDir (project := project) (toolchain := toolchain)
  logInfo m!"CA registry: {s.entries} entries — {s.openPoints} open points ({s.openProved} proved), {s.published} published: {s.proved} proved, {s.conditional} conditional, {s.definitions} definitions, {s.axioms} axioms"
  logInfo m!"{if s.changed then "Wrote" else "Unchanged"} {s.declsPath}, {s.metaPath}"

/-- `#ca_registry "output_dir/"` — generates `declarations.json` and `meta.json`
    from `@[publish]` and `@[open_point]` annotations in the current environment.
    Place at the end of your registry file so `lake build` produces the registry. -/
elab "#ca_registry " dir:str : command => do
  generateRegistryFiles dir.getString

end CA.Registry

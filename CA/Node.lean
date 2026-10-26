import Lean
import CA.Payload
import CA.Registry.Generate
import CA.Ed25519

/-!
# CA.Node — the contents of a registry node (`registry-protocol.md` §12)

A node, as published, is a set of rows: the file's ref and name tables,
units, members, decorations (`docs/payload.md` §6), and the declaration,
witness, statement and entry rows that index them. This module builds
those rows from declarations and the ids of what they reference
(`packDecls`, no `Environment` needed: a store such as canode's packs
from what it holds), or from a Lean environment (`packEnvironment`), and
checks a set of rows (`checkNode`). It holds no file format: the `ca` CLI writes and
reads the rows as one SQLite file (`ca pack`, `ca check`), and any other
store can hold the same rows.
-/

open Lean
open CA.RefHash (RefTable DeclIds)
open CA.Payload

namespace CA.Node

structure UnitRow where
  key : ByteArray
  /-- SHA-256 of `bytes`: naming variants of one key are told apart by it. -/
  variant : ByteArray
  form : Form
  bytes : ByteArray
  deriving Inhabited

structure MemberRow where
  decl : ByteArray
  name : Name
  key : ByteArray
  variant : ByteArray
  member : Nat
  deriving Inhabited

structure DecorationRow where
  decl : ByteArray
  name : Name
  bytes : ByteArray
  deriving Inhabited

structure DeclRow where
  decl : ByteArray
  kind : String
  stmt : ByteArray
  ref : ByteArray
  deriving Inhabited

/-- A registry entry (`@[publish]` / `@[open_point]`): its statement unit is
    in `units` under `stmt`. -/
structure EntryRow where
  name : Name
  stmt : ByteArray
  status : String
  typeHash : String
  deriving Inhabited

/-- A dependency edge: `decl` cites `ref` (`registry-protocol.md` §4). Only
    references outside the declaration's own unit; siblings of a block are
    not dependencies but members. -/
structure DepRow where
  decl : ByteArray
  ref : ByteArray
  deriving Inhabited

/-- A verification record as stored (`registry-protocol.md` §3): the JSON
    `CA.Verify.Record.toJson` produces, its digest, and the signer's key
    and signature over the digest (empty when unsigned). -/
structure RecordRow where
  decl : ByteArray
  digest : ByteArray
  json : String
  signer : String := ""
  sig : ByteArray := .empty
  valid : Bool
  deriving Inhabited

/-- A namespace claim (`registry-protocol.md` §7): `ns` is `label@key`,
    `key` the owner's base58 public key; signed by the owner. -/
structure NamespaceRow where
  ns : String
  ownerKey : ByteArray
  /-- JSON array of base58 delegate keys. -/
  delegates : String := "[]"
  sig : ByteArray
  deriving Inhabited

/-- A binding `(ns, name) ↦ target` with a sequence number, signed by the
    namespace's owner or a delegate; the highest `seq` wins on merge. -/
structure BindingRow where
  ns : String
  name : Name
  seq : Nat
  /-- A `ref` id (or empty: unbound). -/
  target : ByteArray
  sig : ByteArray
  deriving Inhabited

structure Node where
  info : Array (String × String) := #[]
  table : FileTable := {}
  units : Array UnitRow := #[]
  members : Array MemberRow := #[]
  decorations : Array DecorationRow := #[]
  declarations : Array DeclRow := #[]
  /-- (`stmt`, `decl`) for every theorem: the witnesses of a statement. -/
  witnesses : Array (ByteArray × ByteArray) := #[]
  entries : Array EntryRow := #[]
  /-- The `ref` ids each packed declaration cites outside its unit. -/
  deps : Array DepRow := #[]
  records : Array RecordRow := #[]
  namespaces : Array NamespaceRow := #[]
  bindings : Array BindingRow := #[]
  deriving Inhabited

/-! ## Signing (`CA.Ed25519`) -/

/-- A public key as it appears in namespace ids and record signers. -/
def keyText (pk : ByteArray) : String := CA.RefHash.toB58 pk

def keyOfText (s : String) : Option ByteArray :=
  match CA.Base58.decode s with
  | some b => if b.size == 32 then some b else none
  | none => none

/-- The owner key named in a namespace id `label@key`. -/
def namespaceKey (ns : String) : Option ByteArray :=
  match ns.splitOn "@" with
  | [_, k] => keyOfText k
  | _ => none

def namespaceId (label : String) (pk : ByteArray) : String := s!"{label}@{keyText pk}"

private def u64be (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for i in [:8] do b := b.push ((n >>> (8 * (7 - i))) % 256).toUInt8
  return b

/-- The bytes a namespace claim signs. -/
def namespaceMessage (ns : String) (ownerKey : ByteArray) (delegates : String) : ByteArray :=
  "CA-namespace-1\n".toUTF8 ++ ns.toUTF8 ++ ⟨#[0]⟩ ++ ownerKey ++ delegates.toUTF8

/-- The bytes a binding signs. -/
def bindingMessage (ns : String) (name : Name) (seq : Nat) (target : ByteArray) : ByteArray :=
  "CA-binding-1\n".toUTF8 ++ ns.toUTF8 ++ ⟨#[0]⟩ ++ CA.Payload.putName .empty name ++ u64be seq ++ target

/-- Claim the namespace `label@key` for `seed`'s key. -/
def claimNamespace (seed : ByteArray) (label : String) : NamespaceRow :=
  let pk := CA.Ed25519.publicKey seed
  let ns := namespaceId label pk
  { ns, ownerKey := pk, sig := CA.Ed25519.sign seed (namespaceMessage ns pk "[]") }

/-- Bind every registry entry of `node` in `label@key`: name ↦ the `ref` of
    its declaration (its `stmt` for an entry whose declaration is not in the
    file). Appends the claim and the bindings; `seq` for every binding. -/
def bindEntries (node : Node) (seed : ByteArray) (label : String) (seq : Nat := 1) : Node := Id.run do
  let claim := claimNamespace seed label
  let declOf : Std.HashMap Name ByteArray := node.members.foldl (fun m r => m.insert r.name r.decl) {}
  let refOf : Std.HashMap ByteArray ByteArray := node.declarations.foldl (fun m d => m.insert d.decl d.ref) {}
  let mut bs := node.bindings
  for e in node.entries do
    let target := match declOf.get? e.name >>= refOf.get? with
      | some r => r
      | none => e.stmt
    bs := bs.push { ns := claim.ns, name := e.name, seq, target,
                    sig := CA.Ed25519.sign seed (bindingMessage claim.ns e.name seq target) }
  return { node with namespaces := node.namespaces.push claim, bindings := bs }

/-- Faults in the signed rows: claims not signed by their key, bindings not
    signed by their namespace's owner or a delegate or pointing at nothing
    in the file, records whose signer does not verify. -/
def checkSigned (node : Node) : Array String := Id.run do
  let mut faults := #[]
  let mut owners : Std.HashMap String (Array ByteArray) := {}
  for c in node.namespaces do
    match namespaceKey c.ns with
    | none => faults := faults.push s!"namespace {c.ns}: id is not label@key"
    | some k =>
      if k != c.ownerKey then faults := faults.push s!"namespace {c.ns}: owner key is not the key in the id"
      else if !CA.Ed25519.verify k (namespaceMessage c.ns c.ownerKey c.delegates) c.sig then
        faults := faults.push s!"namespace {c.ns}: claim signature does not verify"
      else
        let delegates : Array ByteArray := match Lean.Json.parse c.delegates with
          | .ok (.arr a) => a.filterMap fun j => j.getStr?.toOption.bind keyOfText
          | _ => #[]
        owners := owners.insert c.ns (#[k] ++ delegates)
  let targets : Std.HashSet ByteArray :=
    (node.declarations.foldl (fun s d => s.insert d.ref) {}) |> node.units.foldl (fun s u => s.insert u.key)
  for b in node.bindings do
    match owners.get? b.ns with
    | none => faults := faults.push s!"binding {b.ns} {b.name}: no claim for its namespace in the file"
    | some keys =>
      let msg := bindingMessage b.ns b.name b.seq b.target
      unless keys.any (fun k => CA.Ed25519.verify k msg b.sig) do
        faults := faults.push s!"binding {b.ns} {b.name} #{b.seq}: not signed by the owner or a delegate"
      if !b.target.isEmpty && !targets.contains b.target then
        faults := faults.push s!"binding {b.ns} {b.name} #{b.seq}: target {CA.RefHash.toB58 b.target} is not in the file"
  for r in node.records do
    unless r.signer.isEmpty do
      match keyOfText r.signer with
      | none => faults := faults.push s!"record for {CA.RefHash.toB58 r.decl}: signer is not a key"
      | some k =>
        unless CA.Ed25519.verify k r.digest r.sig do
          faults := faults.push s!"record for {CA.RefHash.toB58 r.decl}: signature by {r.signer} does not verify"
  return faults

/-! ## Packing -/

/-- Closure of `roots` under `RefHash.refsOf` (with or without proofs). -/
def coneOf (env : Environment) (roots : Array Name) (withProofs : Bool) :
    Array (Name × ConstantInfo) := Id.run do
  let mut seen : NameSet := {}
  let mut out := #[]
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    out := out.push (n, ci)
    for m in (RefHash.refsOf ci withProofs).toArray do
      if !seen.contains m then stack := stack.push m
  return out

structure PackReport where
  declarations : Nat := 0
  units : Nat := 0
  statements : Nat := 0
  /-- Members that did not rebuild exactly; their units are still packed. -/
  inexact : Array Name := #[]
  errors : Array String := #[]
  unresolved : Nat := 0
  deriving Inhabited

/-- `X.rec`, `X.rec_1`, …: the names the kernel gives recursors. -/
def isRecursorName (n : Name) : Bool :=
  match n with
  | .str _ s => s == "rec" || (s.startsWith "rec_" && (s.drop 4).all Char.isDigit)
  | _ => false

/-- The declarations hashed in one block with `ci`, by the declaration's own
    fields: mutual siblings, an inductive's constructors, a constructor's
    inductive. Hashing `ci` without all of them gives other ids, and no
    by-name fallback reports it (the standalone encoding does not mention
    siblings), so `packDecls` refuses a block with a member missing. -/
def blockSiblings (ci : ConstantInfo) : List Name :=
  let others (ns : List Name) := ns.filter (· != ci.name)
  match ci with
  | .defnInfo v => others v.all
  | .thmInfo v => others v.all
  | .opaqueInfo v => others v.all
  | .inductInfo v => others v.all ++ v.ctors
  | .ctorInfo v => [v.induct]
  | .recInfo v =>
    -- The recursors of a mutual or nested family call each other from
    -- their rules (`A.rec` ↔ `B.rec`, `T.rec` ↔ `T.rec_1`): one block.
    let called := v.rules.foldl (fun a r => CA.Util.collectConstants r.rhs a) ({} : NameSet)
    called.toList.filter fun n => n != ci.name && isRecursorName n
  | _ => []

/-- Build the declaration rows of a node from declarations alone, with no
    `Environment`. `decls` holds every declaration to hash: each root with
    its whole block (with a member left out the ids differ, so nothing is
    packed and `errors` names it). `base` gives the ids of everything they reference that is not
    in `decls`. `roots` (default: all of `decls`) are packed; the rest of
    `decls` is hashed, so roots can cite it by id, but not packed. Returns
    the ids `CA.RefHash` gave every declaration in `decls` as well, so a
    store can compare them with the ids it holds. -/
def packDecls (decls : Array (Name × ConstantInfo)) (base : RefTable)
    (roots : Array Name := decls.map (·.1)) (withProofs : Bool := true)
    (hasher : CA.SHA256.Hasher := CA.SHA256.pureHasher)
    (info : Array (String × String) := #[]) (selfCheck : Bool := true) (withDeps : Bool := true) :
    IO (Node × PackReport × Array DeclIds) := do
  let find : Std.HashMap Name ConstantInfo := decls.foldl (fun m (n, ci) => m.insert n ci) {}
  let mut missing : Array String := #[]
  for (n, ci) in decls do
    for m in blockSiblings ci do
      if !find.contains m then missing := missing.push s!"{n}: block member {m} is not given"
  if !missing.isEmpty then
    return ({ info }, { errors := missing }, #[])
  let (ids, table) ← RefHash.computeIds decls base hasher withProofs
  let byName : Std.HashMap Name DeclIds := ids.foldl (fun m d => m.insert d.name d) {}
  -- Blocks by id; twin blocks share an id, so split by the reference graph.
  let mut byBlock : Std.HashMap ByteArray (Array Name) := {}
  for d in ids do
    if let some (b, _) := d.block then byBlock := byBlock.insert b ((byBlock.getD b #[]).push d.name)
  let mut sccOf : Std.HashMap Name (Array Name) := {}
  for (_, g) in byBlock.toArray do
    let succ (n : Name) : Array Name :=
      match find.get? n with
      | some ci => (RefHash.refsOf ci withProofs).toArray
      | none => #[]
    for comp in RefHash.sccs g succ do
      for n in comp do sccOf := sccOf.insert n comp
  let mut node : Node := { info }
  let mut rep : PackReport := {}
  let mut done : NameSet := {}
  let mut seenUnit : Std.HashSet (ByteArray × ByteArray) := {}
  for r in roots do
    if done.contains r then continue
    let some d := byName.get? r | rep := { rep with errors := rep.errors.push s!"{r}: no ids" }; continue
    let comp := if d.block.isSome then sccOf.getD r #[r] else #[r]
    let mut input := #[]
    for n in comp do
      done := done.insert n
      if let some ci := find.get? n then input := input.push (n, ci)
    -- The ids were computed once above; the encoder need not recompute them.
    let knownIds : Option (Array DeclIds) := input.mapM fun (n, _) => byName.get? n
    match ← encodeUnit input table node.table hasher withProofs knownIds selfCheck with
    | .error e => rep := { rep with errors := rep.errors.push s!"{r}: {e}" }
    | .ok (enc, ft) =>
      node := { node with table := ft }
      if !enc.exact then rep := { rep with inexact := rep.inexact ++ enc.inexact }
      let variant ← hasher enc.bytes
      if !seenUnit.contains (enc.key, variant) then
        seenUnit := seenUnit.insert (enc.key, variant)
        node := { node with units := node.units.push ⟨enc.key, variant, enc.form, enc.bytes⟩ }
        rep := { rep with units := rep.units + 1 }
      let compSet : NameSet := comp.foldl (·.insert ·) {}
      for i in [:enc.ids.size] do
        let di := enc.ids[i]!
        let ci := find.get! di.name
        rep := { rep with unresolved := rep.unresolved + di.unresolved.size,
                          declarations := rep.declarations + 1 }
        -- Dependencies: the references outside this unit, by ref id. Derivable
        -- from the unit (a checker confirms them against its slots), so a pack
        -- may leave them out: on Init they are 1.16 M rows, more than the units.
        let mut seenRef : Std.HashSet ByteArray := {}
        for m in (if withDeps then (RefHash.refsOf ci withProofs).toList else []) do
          if compSet.contains m then continue
          if let some r := table.get? m then
            if !seenRef.contains r then
              seenRef := seenRef.insert r
              node := { node with deps := node.deps.push ⟨di.decl, r⟩ }
        node := { node with
          members := node.members.push ⟨di.decl, di.name, enc.key, variant, i⟩
          decorations := node.decorations.push ⟨di.decl, di.name, enc.decorations[i]!.2⟩
          declarations := node.declarations.push ⟨di.decl, CA.Util.constantKind ci, di.stmt, di.ref⟩ }
        if let .thmInfo _ := ci then
          node := { node with witnesses := node.witnesses.push (di.stmt, di.decl) }
  -- Deduplicate declaration rows (twins are separate members, one decl).
  let mut seenDecl : Std.HashSet ByteArray := {}
  let mut rows := #[]
  for d in node.declarations do
    if !seenDecl.contains d.decl then
      seenDecl := seenDecl.insert d.decl
      rows := rows.push d
  let mut seenW : Std.HashSet (ByteArray × ByteArray) := {}
  let mut ws := #[]
  for w in node.witnesses do
    if !seenW.contains w then
      seenW := seenW.insert w
      ws := ws.push w
  let mut seenDep : Std.HashSet (ByteArray × ByteArray) := {}
  let mut deps := #[]
  for d in node.deps do
    if !seenDep.contains (d.decl, d.ref) then
      seenDep := seenDep.insert (d.decl, d.ref)
      deps := deps.push d
  return ({ node with declarations := rows, witnesses := ws, deps }, rep, ids)

/-- Build a node from `env`. `roots` are the declarations to pack (each
    with its whole block); their dependencies are referenced by id, not
    packed. With `withProofs := false` theorems are packed in statement
    mode. Registry entries (`@[publish]` / `@[open_point]`) get a
    statement unit and an entry row. `cacheDir` caches the imported part
    of the reference table, as `#ca_registry` does. The rows themselves
    come from `packDecls`. -/
def packEnvironment (env : Environment) (roots : Array Name) (withProofs : Bool := true)
    (hasher : CA.SHA256.Hasher := CA.SHA256.pureHasher)
    (cacheDir : Option System.FilePath := some CA.Registry.defaultCacheDir)
    (info : Array (String × String) := #[]) (selfCheck : Bool := true) (withDeps : Bool := true) :
    IO (Node × PackReport) := do
  let cone := coneOf env roots withProofs
  let cachePath ← match cacheDir with
    | some d =>
      pure (some (d / s!"reftable-{if withProofs then "full" else "stmt"}-{← CA.Registry.importsCacheKey env}.bin"))
    | none => pure none
  let base : RefTable ← match cachePath with
    | some p => pure ((← CA.Registry.readRefTable p).getD {})
    | none => pure {}
  let rootSet : NameSet := roots.foldl (·.insert ·) {}
  let todo := cone.filter fun (n, _) => rootSet.contains n || !base.contains n
  let (node0, rep0, ids) ← packDecls todo base roots withProofs hasher info selfCheck withDeps
  let mut node := node0
  let mut rep := rep0
  if let some p := cachePath then
    let mut cache := base
    for d in ids do
      if d.unresolved.isEmpty && (env.getModuleIdxFor? d.name).isSome then
        cache := cache.insert d.name d.ref
    if cache.size > base.size then
      try CA.Registry.writeRefTable p cache catch _ => pure ()
  -- Registry entries: statement units and entry rows.
  let mut seenUnit : Std.HashSet (ByteArray × ByteArray) :=
    node.units.foldl (fun s u => s.insert (u.key, u.variant)) {}
  let ann := CA.Registry.annotated env
  if !ann.isEmpty then
    let (eids, stable) ← CA.Registry.computeEntryIdsAndTable env (ann.map (·.1)) hasher cacheDir
    for e in CA.Registry.classify env eids do
      match ← encodeStatement e.ci.levelParams (CA.Registry.hashTarget e.ci) stable node.table hasher
          (own := e.name) with
      | .error err => rep := { rep with errors := rep.errors.push s!"{e.name}: statement: {err}" }
      | .ok (enc, ft) =>
        if enc.key != e.stmt || !enc.exact then
          rep := { rep with errors := rep.errors.push s!"{e.name}: statement unit does not check" }
          continue
        node := { node with table := ft }
        let variant ← hasher enc.bytes
        if !seenUnit.contains (enc.key, variant) then
          seenUnit := seenUnit.insert (enc.key, variant)
          node := { node with units := node.units.push ⟨enc.key, variant, .statement, enc.bytes⟩ }
        -- The statement's decoration, keyed by (stmt, entry name): what lets
        -- a reader rebuild the statement with its names (`CA.Verify`).
        if let some d := enc.decorations[0]? then
          node := { node with decorations := node.decorations.push ⟨e.stmt, e.name, d.2⟩ }
        node := { node with entries := node.entries.push ⟨e.name, e.stmt, e.status.toString, e.address⟩ }
        rep := { rep with statements := rep.statements + 1 }
  return (node, rep)

/-! ## Checking -/

structure CheckReport where
  units : Nat := 0
  members : Nat := 0
  decorations : Nat := 0
  /-- Members rebuilt from their decorations whose recomputed ids match. -/
  rebuilt : Nat := 0
  /-- Keys holding more than one unit. -/
  namingVariants : Nat := 0
  /-- Units that do not check to their key, rows that disagree with the
      units: each one a reason to distrust the file. -/
  faults : Array String := #[]
  /-- Units with names hashed by name (`spec.md` §10). -/
  inexact : Nat := 0
  deriving Inhabited

/-- Rows of a node as stored, from `CA.Verify`'s records: the JSON, its
    digest, and a signature when `seed` is given. -/
def recordRows (records : Array (ByteArray × Bool × Lean.Json)) (seed : Option ByteArray := none)
    (hasher : CA.SHA256.Hasher := CA.SHA256.pureHasher) : IO (Array RecordRow) :=
  records.mapM fun (decl, valid, j) => do
    let json := j.compress
    let digest ← hasher json.toUTF8
    match seed with
    | some s => return { decl, digest, json, valid, signer := keyText (CA.Ed25519.publicKey s),
                         sig := CA.Ed25519.sign s digest }
    | none => return { decl, digest, json, valid }

/-- Check every row of a node against its units (`registry-protocol.md`
    §5): each unit's ids are recomputed from its bytes and the ref table;
    every member, declaration, witness and entry row must agree with
    them; every decoration must rebuild declarations whose ids, computed
    from the names it gives and the ids those names stand for in the
    file, are the unit's. -/
def checkNode (node : Node) (hasher : CA.SHA256.Hasher := CA.SHA256.pureHasher) :
    IO CheckReport := do
  let mut rep : CheckReport := {}
  let mut checked : Std.HashMap (ByteArray × ByteArray) (UnitData × Checked) := {}
  let mut variantsOf : Std.HashMap ByteArray Nat := {}
  for u in node.units do
    rep := { rep with units := rep.units + 1 }
    variantsOf := variantsOf.insert u.key (variantsOf.getD u.key 0 + 1)
    let k := RefHash.toB58 u.key
    if (← hasher u.bytes) != u.variant then
      rep := { rep with faults := rep.faults.push s!"unit {k}: variant is not the digest of its bytes" }
      continue
    match decodeUnit u.bytes with
    | .error e => rep := { rep with faults := rep.faults.push s!"unit {k}: {e}" }
    | .ok d =>
      if d.form != u.form then
        rep := { rep with faults := rep.faults.push s!"unit {k}: form column disagrees with the bytes" }
      match ← checkUnit d node.table.refs hasher with
      | .error e => rep := { rep with faults := rep.faults.push s!"unit {k}: {e}" }
      | .ok c =>
        if c.key != u.key then
          rep := { rep with faults := rep.faults.push s!"unit {k}: checks to {RefHash.toB58 c.key}" }
        else
          if !c.unresolved.isEmpty then rep := { rep with inexact := rep.inexact + 1 }
          checked := checked.insert (u.key, u.variant) (d, c)
  rep := { rep with namingVariants := variantsOf.fold (fun n _ c => if c > 1 then n + 1 else n) 0 }
  -- Dependencies: every `deps` row of a member cites one of its unit's
  -- reference slots, and the members of a unit together cite every slot.
  let depsOf : Std.HashMap ByteArray (Array ByteArray) :=
    node.deps.foldl (fun m d => m.insert d.decl ((m.getD d.decl #[]).push d.ref)) {}
  let mut unitRefs : Std.HashMap (ByteArray × ByteArray) (Std.HashSet ByteArray) := {}
  for ((k, v), (u, _)) in checked.toArray do
    let s := u.refs.foldl (fun (s : Std.HashSet ByteArray) p =>
      match node.table.refs[p]? with | some r => s.insert r | none => s) {}
    unitRefs := unitRefs.insert (k, v) s
  rep := { rep with faults := rep.faults ++ checkSigned node }
  -- Records: digest of the JSON, a declaration row for the decl, the same stmt.
  let declStmt : Std.HashMap ByteArray ByteArray :=
    node.declarations.foldl (fun m d => m.insert d.decl d.stmt) {}
  for r in node.records do
    let k := RefHash.toB58 r.decl
    if (← hasher r.json.toUTF8) != r.digest then
      rep := { rep with faults := rep.faults.push s!"record for {k}: digest is not the hash of its JSON" }
    match declStmt.get? r.decl with
    | none => rep := { rep with faults := rep.faults.push s!"record for {k}: no such declaration in the file" }
    | some stmt =>
      match Lean.Json.parse r.json with
      | .error e => rep := { rep with faults := rep.faults.push s!"record for {k}: {e}" }
      | .ok j =>
        if (j.getObjValAs? String "stmt").toOption != some (RefHash.toB58 stmt) then
          rep := { rep with faults := rep.faults.push s!"record for {k}: stmt differs from the declaration's" }
        if (j.getObjValAs? String "decl").toOption != some k then
          rep := { rep with faults := rep.faults.push s!"record for {k}: decl field differs from the row's" }
  if !node.deps.isEmpty then
    let mut cited : Std.HashMap (ByteArray × ByteArray) (Std.HashSet ByteArray) := {}
    for m in node.members do
      let some s := unitRefs.get? (m.key, m.variant) | continue
      let mut c := cited.getD (m.key, m.variant) {}
      for r in depsOf.getD m.decl #[] do
        if !s.contains r then
          rep := { rep with faults := rep.faults.push s!"deps {m.name}: cites {RefHash.toB58 r}, not a reference of its unit" }
        c := c.insert r
      cited := cited.insert (m.key, m.variant) c
    for ((k, v), s) in unitRefs.toArray do
      let c := cited.getD (k, v) {}
      if (cited.contains (k, v)) && s.toArray.any (!c.contains ·) then
        rep := { rep with faults := rep.faults.push s!"deps of unit {RefHash.toB58 k}: a reference of the unit is cited by no member" }
  -- Members agree with their unit.
  let decoOf : Std.HashMap (ByteArray × Name) ByteArray :=
    node.decorations.foldl (fun m d => m.insert (d.decl, d.name) d.bytes) {}
  let mut byUnit : Std.HashMap (ByteArray × ByteArray) (Array MemberRow) := {}
  for m in node.members do
    rep := { rep with members := rep.members + 1 }
    match checked.get? (m.key, m.variant) with
    | none => rep := { rep with faults := rep.faults.push s!"member {m.name}: its unit is missing or faulty" }
    | some (_, c) =>
      match c.ids[m.member]? with
      | some (_, d, _) =>
        if d != m.decl then
          rep := { rep with faults := rep.faults.push s!"member {m.name}: listed decl is not member {m.member}'s" }
        else byUnit := byUnit.insert (m.key, m.variant) ((byUnit.getD (m.key, m.variant) #[]).push m)
      | none => rep := { rep with faults := rep.faults.push s!"member {m.name}: no member {m.member}" }
  -- Decorations rebuild declarations with the unit's ids.
  for (k, ms) in byUnit.toArray do
    let some (u, _) := checked.get? k | continue
    -- One decoration per member index (the first name found for it).
    let mut pick : Array (Option (Name × Decoration)) := Array.replicate u.members.size none
    for m in ms do
      if pick[m.member]!.isSome then continue
      match decoOf.get? (m.decl, m.name) with
      | none => rep := { rep with faults := rep.faults.push s!"member {m.name}: no decoration" }
      | some b =>
        rep := { rep with decorations := rep.decorations + 1 }
        match decodeDecoration b with
        | .error e => rep := { rep with faults := rep.faults.push s!"decoration {m.name}: {e}" }
        | .ok d => pick := pick.set! m.member (some (m.name, d))
    if pick.any (·.isNone) then continue
    let decos := pick.filterMap (·.map (·.2))
    match rebuild u node.table decos with
    | .error e => rep := { rep with faults := rep.faults.push s!"rebuild {decos[0]!.own}: {e}" }
    | .ok back =>
      -- The ids the decorations' names stand for, as given by the file.
      let mut base : RefTable := {}
      for d in decos do
        for j in [:u.refs.size] do
          if let (some ni, some ri) := (d.refNames[j]?, u.refs[j]?) then
            if let (some n, some id) := (node.table.names[ni]?, node.table.refs[ri]?) then
              base := base.insert n id
      let withProofs := u.members.all fun m => match m.fields with | .thm none _ => false | _ => true
      let (again, _) ← RefHash.computeIds back base hasher withProofs
      let some (_, c) := checked.get? k | continue
      for i in [:again.size] do
        let (_, d, _) := c.ids[i]!
        if again[i]!.decl == d then rep := { rep with rebuilt := rep.rebuilt + 1 }
        else rep := { rep with faults := rep.faults.push s!"rebuild {again[i]!.name}: ids differ from the unit's" }
  -- Declaration and witness rows agree with the units.
  let mut idsOfDecl : Std.HashMap ByteArray (ByteArray × ByteArray) := {}
  for (_, (_, c)) in checked.toArray do
    for (s, d, r) in c.ids do idsOfDecl := idsOfDecl.insert d (s, r)
  for d in node.declarations do
    match idsOfDecl.get? d.decl with
    | some (s, r) =>
      if s != d.stmt || r != d.ref then
        rep := { rep with faults := rep.faults.push s!"declaration {RefHash.toB58 d.decl}: stmt / ref disagree" }
    | none => rep := { rep with faults := rep.faults.push s!"declaration {RefHash.toB58 d.decl}: no unit" }
  for (s, d) in node.witnesses do
    if (idsOfDecl.get? d).map (·.1) != some s then
      rep := { rep with faults := rep.faults.push s!"witness {RefHash.toB58 d}: not a witness of {RefHash.toB58 s}" }
  for e in node.entries do
    if !(variantsOf.contains e.stmt) then
      rep := { rep with faults := rep.faults.push s!"entry {e.name}: no statement unit" }
  return rep


/-! ## Merge (`registry-protocol.md` §6)

Union per key: units and decorations re-encoded against the merged
file's tables (ids unchanged, variant digests recomputed), members and
declaration rows carried over, witnesses, deps and records unioned,
entries keyed by (name, stmt), namespace claims by id, bindings by the
highest sequence number (ties on signature bytes). Faults are not judged
here: run `checkNode` on the result, as `ca merge` does. -/

/-- Add every row of `b` to `a`. -/
def merge (a b : Node) (hasher : CA.SHA256.Hasher := CA.SHA256.pureHasher) : IO (Node × Array String) := do
  let mut out := a
  let mut errors : Array String := #[]
  let mut units : Std.HashSet (ByteArray × ByteArray) := a.units.foldl (fun s u => s.insert (u.key, u.variant)) {}
  -- Old (key, variant) of b → new variant in the merged file.
  let mut newVariant : Std.HashMap (ByteArray × ByteArray) ByteArray := {}
  for u in b.units do
    match decodeUnit u.bytes with
    | .error e => errors := errors.push s!"unit {RefHash.toB58 u.key}: {e}"
    | .ok d =>
      match remapUnit d b.table out.table with
      | .error e => errors := errors.push s!"unit {RefHash.toB58 u.key}: {e}"
      | .ok (d', ft) =>
        out := { out with table := ft }
        let bytes := d'.toBytes
        let variant ← hasher bytes
        newVariant := newVariant.insert (u.key, u.variant) variant
        if !units.contains (u.key, variant) then
          units := units.insert (u.key, variant)
          out := { out with units := out.units.push ⟨u.key, variant, u.form, bytes⟩ }
  let mut members : Std.HashSet (ByteArray × Name) := a.members.foldl (fun s m => s.insert (m.decl, m.name)) {}
  for m in b.members do
    let some v := newVariant.get? (m.key, m.variant) | continue
    if !members.contains (m.decl, m.name) then
      members := members.insert (m.decl, m.name)
      out := { out with members := out.members.push { m with variant := v } }
  let mut decos : Std.HashSet (ByteArray × Name) := a.decorations.foldl (fun s d => s.insert (d.decl, d.name)) {}
  for d in b.decorations do
    if decos.contains (d.decl, d.name) then continue
    match decodeDecoration d.bytes with
    | .error e => errors := errors.push s!"decoration {d.name}: {e}"
    | .ok de =>
      match remapDecoration de b.table out.table with
      | .error e => errors := errors.push s!"decoration {d.name}: {e}"
      | .ok (de', ft) =>
        out := { out with table := ft }
        decos := decos.insert (d.decl, d.name)
        out := { out with decorations := out.decorations.push ⟨d.decl, d.name, de'.toBytes⟩ }
  let declSet : Std.HashSet ByteArray := a.declarations.foldl (fun s d => s.insert d.decl) {}
  let mut declSet := declSet
  for d in b.declarations do
    if !declSet.contains d.decl then
      declSet := declSet.insert d.decl
      out := { out with declarations := out.declarations.push d }
  let mut ws : Std.HashSet (ByteArray × ByteArray) := a.witnesses.foldl (·.insert ·) {}
  for w in b.witnesses do
    if !ws.contains w then ws := ws.insert w; out := { out with witnesses := out.witnesses.push w }
  let mut deps : Std.HashSet (ByteArray × ByteArray) := a.deps.foldl (fun s d => s.insert (d.decl, d.ref)) {}
  for d in b.deps do
    if !deps.contains (d.decl, d.ref) then deps := deps.insert (d.decl, d.ref); out := { out with deps := out.deps.push d }
  let mut entries : Std.HashSet (Name × ByteArray) := a.entries.foldl (fun s e => s.insert (e.name, e.stmt)) {}
  for e in b.entries do
    if !entries.contains (e.name, e.stmt) then
      entries := entries.insert (e.name, e.stmt); out := { out with entries := out.entries.push e }
  let mut recs : Std.HashSet ByteArray := a.records.foldl (fun s r => s.insert r.digest) {}
  for r in b.records do
    if !recs.contains r.digest then recs := recs.insert r.digest; out := { out with records := out.records.push r }
  let mut nss : Std.HashSet String := a.namespaces.foldl (fun s c => s.insert c.ns) {}
  for c in b.namespaces do
    if !nss.contains c.ns then nss := nss.insert c.ns; out := { out with namespaces := out.namespaces.push c }
  -- Bindings: the highest sequence number per (ns, name); ties on signature bytes.
  let mut best : Std.HashMap (String × Name) BindingRow := {}
  for r in a.bindings ++ b.bindings do
    match best.get? (r.ns, r.name) with
    | none => best := best.insert (r.ns, r.name) r
    | some cur =>
      if r.seq > cur.seq || (r.seq == cur.seq && r.sig.toList > cur.sig.toList) then
        best := best.insert (r.ns, r.name) r
  out := { out with bindings := (best.toArray.map (·.2)).qsort fun x y => x.ns < y.ns || (x.ns == y.ns && Name.lt x.name y.name) }
  -- Manifest: what was merged.
  let projects := ((a.info.filter (·.1 == "project")) ++ (b.info.filter (·.1 == "project"))).map (·.2)
  let info := (a.info.filter fun (k, _) => k != "project" && k != "node" && k != "proofs") ++
    #[("node", "merged"), ("project", ", ".intercalate projects.toList)]
  return ({ out with info }, errors)

/-! ## Range digests (`registry-protocol.md` §10)

Two nodes find what they lack by exchanging digests of id ranges and
recursing only into the ranges that differ. Here a range is a prefix of
the id (`bits` bits, so `2 ^ bits` buckets) and its digest is the hash of
its sorted ids. The ids are the node's content keys: unit keys and
declaration ids. -/

/-- The content keys of a node, sorted. -/
def contentKeys (node : Node) : Array ByteArray := Id.run do
  let mut s : Std.HashSet ByteArray := {}
  for u in node.units do s := s.insert u.key
  for d in node.declarations do s := s.insert d.decl
  return s.toArray.qsort fun x y => x.toList < y.toList

def bucketOf (id : ByteArray) (bits : Nat) : Nat :=
  let n := id.data.foldl (fun acc x => acc * 256 + x.toNat) 0   -- big-endian
  n >>> (256 - bits)

/-- `(bucket, digest, count)` for every non-empty bucket. -/
def rangeDigests (node : Node) (bits : Nat := 8) (hasher : CA.SHA256.Hasher := CA.SHA256.pureHasher) :
    IO (Array (Nat × ByteArray × Nat)) := do
  let keys := contentKeys node
  let mut out := #[]
  let mut cur : Option Nat := none
  let mut acc : ByteArray := .empty
  let mut n := 0
  for k in keys do
    let b := bucketOf k bits
    if cur != some b then
      if let some c := cur then out := out.push (c, ← hasher acc, n)
      cur := some b; acc := .empty; n := 0
    acc := acc ++ k; n := n + 1
  if let some c := cur then out := out.push (c, ← hasher acc, n)
  return out

/-- Keys of `a` not in `b` and of `b` not in `a`, found by comparing bucket
    digests first; returns also how many buckets were compared and how
    many had to be opened. -/
def diff (a b : Node) (bits : Nat := 8) (hasher : CA.SHA256.Hasher := CA.SHA256.pureHasher) :
    IO (Array ByteArray × Array ByteArray × Nat × Nat) := do
  let da ← rangeDigests a bits hasher
  let db ← rangeDigests b bits hasher
  let ma : Std.HashMap Nat ByteArray := da.foldl (fun m (c, d, _) => m.insert c d) {}
  let mb : Std.HashMap Nat ByteArray := db.foldl (fun m (c, d, _) => m.insert c d) {}
  let buckets : Std.HashSet Nat := (da.foldl (fun s (c, _, _) => s.insert c) {}) |> db.foldl (fun s (c, _, _) => s.insert c)
  let mut opened : Array Nat := #[]
  for c in buckets.toArray do
    if ma.get? c != mb.get? c then opened := opened.push c
  let openedSet : Std.HashSet Nat := opened.foldl (·.insert ·) {}
  let ka := (contentKeys a).filter fun k => openedSet.contains (bucketOf k bits)
  let kb := (contentKeys b).filter fun k => openedSet.contains (bucketOf k bits)
  let sa : Std.HashSet ByteArray := ka.foldl (·.insert ·) {}
  let sb : Std.HashSet ByteArray := kb.foldl (·.insert ·) {}
  return (ka.filter (!sb.contains ·), kb.filter (!sa.contains ·), buckets.size, opened.size)

end CA.Node

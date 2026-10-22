import Lean
import CA.Payload
import CA.Registry.Generate

/-!
# CA.Node — the contents of a registry node (`registry-protocol.md` §12)

A node, as published, is a set of rows: the file's ref and name tables,
units, members, decorations (`docs/payload.md` §6), and the declaration,
witness, statement and entry rows that index them. This module builds
those rows from a Lean environment (`packEnvironment`) and checks a set
of rows (`checkNode`). It holds no file format: the `ca` CLI writes and
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
  deriving Inhabited

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

/-- Build a node from `env`. `roots` are the declarations to pack (each
    with its whole block); their dependencies are referenced by id, not
    packed. With `withProofs := false` theorems are packed in statement
    mode. Registry entries (`@[publish]` / `@[open_point]`) get a
    statement unit and an entry row. `cacheDir` caches the imported part
    of the reference table, as `#ca_registry` does. -/
def packEnvironment (env : Environment) (roots : Array Name) (withProofs : Bool := true)
    (hasher : CA.SHA256.Hasher := CA.SHA256.pureHasher)
    (cacheDir : Option System.FilePath := some CA.Registry.defaultCacheDir)
    (info : Array (String × String) := #[]) : IO (Node × PackReport) := do
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
  let (ids, table) ← RefHash.computeIds todo base hasher withProofs
  if let some p := cachePath then
    let mut cache := base
    for d in ids do
      if d.unresolved.isEmpty && (env.getModuleIdxFor? d.name).isSome then
        cache := cache.insert d.name d.ref
    if cache.size > base.size then
      try CA.Registry.writeRefTable p cache catch _ => pure ()
  let byName : Std.HashMap Name DeclIds := ids.foldl (fun m d => m.insert d.name d) {}
  -- Blocks by id; twin blocks share an id, so split by the reference graph.
  let mut byBlock : Std.HashMap ByteArray (Array Name) := {}
  for d in ids do
    if let some (b, _) := d.block then byBlock := byBlock.insert b ((byBlock.getD b #[]).push d.name)
  let mut sccOf : Std.HashMap Name (Array Name) := {}
  for (_, g) in byBlock.toArray do
    let succ (n : Name) : Array Name :=
      match env.find? n with
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
      if let some ci := env.find? n then input := input.push (n, ci)
    match ← encodeUnit input table node.table hasher withProofs with
    | .error e => rep := { rep with errors := rep.errors.push s!"{r}: {e}" }
    | .ok (enc, ft) =>
      node := { node with table := ft }
      if !enc.exact then rep := { rep with inexact := rep.inexact ++ enc.inexact }
      let variant ← hasher enc.bytes
      if !seenUnit.contains (enc.key, variant) then
        seenUnit := seenUnit.insert (enc.key, variant)
        node := { node with units := node.units.push ⟨enc.key, variant, enc.form, enc.bytes⟩ }
        rep := { rep with units := rep.units + 1 }
      for i in [:enc.ids.size] do
        let di := enc.ids[i]!
        let ci := (env.find? di.name).get!
        rep := { rep with unresolved := rep.unresolved + di.unresolved.size,
                          declarations := rep.declarations + 1 }
        node := { node with
          members := node.members.push ⟨di.decl, di.name, enc.key, variant, i⟩
          decorations := node.decorations.push ⟨di.decl, di.name, enc.decorations[i]!.2⟩
          declarations := node.declarations.push ⟨di.decl, CA.Util.constantKind ci, di.stmt, di.ref⟩ }
        if let .thmInfo _ := ci then
          node := { node with witnesses := node.witnesses.push (di.stmt, di.decl) }
  -- Registry entries: statement units and entry rows.
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
        node := { node with entries := node.entries.push ⟨e.name, e.stmt, e.status.toString, e.address⟩ }
        rep := { rep with statements := rep.statements + 1 }
  -- Deduplicate declaration rows (twins are separate members, one decl).
  let mut seenDecl : Std.HashSet ByteArray := {}
  let mut decls := #[]
  for d in node.declarations do
    if !seenDecl.contains d.decl then
      seenDecl := seenDecl.insert d.decl
      decls := decls.push d
  let mut seenW : Std.HashSet (ByteArray × ByteArray) := {}
  let mut ws := #[]
  for w in node.witnesses do
    if !seenW.contains w then
      seenW := seenW.insert w
      ws := ws.push w
  return ({ node with declarations := decls, witnesses := ws }, rep)

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

end CA.Node

import Lean
import CA.Node

/-!
# CA.Verify — the kernel's verdict on a node

`ca check` shows that a node's ids are honest: every unit's ids are
recomputed from its bytes. This module shows that the mathematics is:
every declaration is rebuilt from its unit and decorations, added to a
Lean environment foundations first, and judged by the kernel
(`Environment.addDeclCore` with checking on). Nothing is trusted from the
file but bytes.

What a reader gets (`registry-protocol.md` §3): for every theorem the
kernel accepts, a **verification record** saying which statements were
*assumed* (ref ids the environment did not have and the file did not
prove: open points, statements kept without proofs, references into
projects not packed) and which *axioms* the proof rests on. A record
with `sorryAx` is invalid, not conditional.

Twin blocks (`Add`/`Mul`: one unit, a decoration per name) are rebuilt
one family at a time; the file does not record which decorations belong
together, so families are aligned by sorted name and checked for
consistency afterwards (constructors name their inductive, `all` lists
match). An alignment that does not check is reported and skipped.
-/

open Lean
open CA.Payload CA.Node

namespace CA.Verify

/-- A verification record (`registry-protocol.md` §3), before signing. -/
structure Record where
  name : Name
  decl : ByteArray
  stmt : ByteArray
  /-- Ref ids assumed as axioms of their statement. -/
  assumes : Array ByteArray
  /-- Axioms the proof rests on, the assumed statements excluded. -/
  axioms : Array Name
  /-- Kernel accepted, and no `sorryAx`. -/
  valid : Bool
  deriving Inhabited

structure Report where
  /-- Declarations added to the environment and accepted by the kernel. -/
  added : Nat := 0
  /-- Declarations already in the environment (imports), compared with the file's. -/
  present : Nat := 0
  /-- Names added as axioms of their statement, with the ref id assumed. -/
  assumed : Array (Name × ByteArray) := #[]
  /-- Recursors and quotients the kernel produced itself, compared with the file's. -/
  generated : Nat := 0
  /-- Kernel rejections, missing references, rows that disagree: reasons to distrust the file. -/
  faults : Array String := #[]
  records : Array Record := #[]
  deriving Inhabited

/-- One name's rebuilt declaration. -/
structure Rebuilt where
  ci : ConstantInfo
  decl : ByteArray
  stmt : ByteArray
  ref : ByteArray
  /-- A theorem kept without its proof (statement mode): assumed, not checked. -/
  statementOnly : Bool
  /-- Ref ids of the constants the decoration names, from the unit's slots. -/
  refIds : Std.HashMap Name ByteArray
  deriving Inhabited

private def b58 := CA.RefHash.toB58

/-- Rebuild every declaration of a node, one `Rebuilt` per bound name.
    Families of twin blocks are aligned by sorted name. -/
def rebuildAll (node : CA.Node.Node) (hasher : CA.SHA256.Hasher := CA.SHA256.pureHasher) :
    IO (Std.HashMap Name Rebuilt × Array String) := do
  let mut out : Std.HashMap Name Rebuilt := {}
  let mut faults : Array String := #[]
  let decoOf : Std.HashMap (ByteArray × Name) ByteArray :=
    node.decorations.foldl (fun m d => m.insert (d.decl, d.name) d.bytes) {}
  let mut byUnit : Std.HashMap (ByteArray × ByteArray) (Array MemberRow) := {}
  for m in node.members do
    byUnit := byUnit.insert (m.key, m.variant) ((byUnit.getD (m.key, m.variant) #[]).push m)
  for u in node.units do
    if u.form == .statement then continue
    let some ms := byUnit.get? (u.key, u.variant) | continue
    let d ← match decodeUnit u.bytes with
      | .ok d => pure d
      | .error e => faults := faults.push s!"unit {b58 u.key}: {e}"; continue
    let ids ← match ← checkUnit d node.table.refs hasher with
      | .ok c => pure c.ids
      | .error e => faults := faults.push s!"unit {b58 u.key}: {e}"; continue
    -- Names per member, sorted; the k-th names of every member form family k.
    let mut namesOf : Array (Array Name) := Array.replicate d.members.size #[]
    for m in ms do
      if m.member < namesOf.size then namesOf := namesOf.modify m.member (·.push m.name)
    namesOf := namesOf.map fun ns => (ns.qsort Name.lt)
    let families := namesOf.foldl (fun n ns => max n ns.size) 0
    for k in [:families] do
      let mut decos : Array Decoration := #[]
      let mut ok := true
      for i in [:d.members.size] do
        let ns := namesOf[i]!
        let some n := ns[min k (ns.size - 1)]? | ok := false; break
        let some (_, declId, _) := ids[i]? | ok := false; break
        match decoOf.get? (declId, n) >>= fun b => (decodeDecoration b).toOption with
        | some de => decos := decos.push de
        | none => ok := false; break
      unless ok do
        faults := faults.push s!"unit {b58 u.key}: a member has no decoration for family {k}"
        continue
      let cis ← match rebuild d node.table decos with
        | .ok cis => pure cis
        | .error e => faults := faults.push s!"unit {b58 u.key}: rebuild: {e}"; continue
      -- Consistency of the family: constructors name their inductive, `all` lists are the family's.
      let own : NameSet := cis.foldl (fun s (n, _) => s.insert n) {}
      let consistent := cis.all fun (_, ci) =>
        match ci with
        | .ctorInfo v => own.contains v.induct
        | .inductInfo v => v.ctors.all own.contains && v.all.all own.contains
        | .recInfo _ => true   -- `all` names the inductives, which live in another unit
        | .defnInfo v => v.all.all own.contains
        | .thmInfo v => v.all.all own.contains
        | .opaqueInfo v => v.all.all own.contains
        | _ => true
      unless consistent do
        faults := faults.push s!"unit {b58 u.key}: family {k} of twin names does not align; skipped"
        continue
      -- Ref ids by name, from the first decoration's slot names and the unit's slots.
      let d0 := decos[0]!
      let mut refIds : Std.HashMap Name ByteArray := {}
      for j in [:d.refs.size] do
        match d0.refNames[j]?, node.table.refs[d.refs[j]!]? with
        | some p, some r => if let some nm := node.table.names[p]? then refIds := refIds.insert nm r
        | _, _ => pure ()
      for i in [:cis.size] do
        let (n, ci) := cis[i]!
        -- Only the names genuinely in family k (a member with fewer names repeats its last).
        if k < namesOf[i]!.size then
          let some (stmt, declId, ref) := ids[i]? | continue
          let statementOnly := match d.members[i]!.fields with | .thm none _ => true | _ => false
          out := out.insert n { ci, decl := declId, stmt, ref, statementOnly, refIds }
  return (out, faults)

/-- The statement units of a node with a decoration, by key: what can be
    assumed by ref id. -/
def statementsOf (node : CA.Node.Node) : Std.HashMap ByteArray (UnitData × Decoration) := Id.run do
  let decoOf : Std.HashMap ByteArray ByteArray :=
    node.decorations.foldl (fun m d => if m.contains d.decl then m else m.insert d.decl d.bytes) {}
  let mut out := {}
  for u in node.units do
    if u.form != .statement then continue
    match decodeUnit u.bytes, decoOf.get? u.key >>= fun b => (decodeDecoration b).toOption with
    | .ok d, some de => out := out.insert u.key (d, de)
    | _, _ => pure ()
  return out

private def kernelMsg (e : Kernel.Exception) : IO String := do
  (e.toMessageData {}).toString

/-- Collect the axioms a constant rests on, in `env`. -/
partial def axiomsOf (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut out : NameSet := {}
  let mut stack := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if let .axiomInfo _ := ci then out := out.insert n
    for m in (CA.RefHash.refsOf ci true).toList do
      if !seen.contains m then stack := stack.push m
  return out

structure VState where
  env : Environment
  rep : Report := {}
  /-- Names whose fate is decided: `true` added or present, `false` failed. -/
  done : Std.HashMap Name Bool := {}
  /-- Names being visited: a reference back into one (mutual `all` fields)
      is not a dependency to wait for. -/
  visiting : NameSet := {}
  /-- Ref ids assumed under each decided name (transitively), for records. -/
  assumesOf : Std.HashMap Name (Array ByteArray) := {}
  /-- Names added as axioms, with the ref id assumed. -/
  assumedIds : Std.HashMap Name ByteArray := {}

abbrev VM := StateRefT VState IO

private def fault (s : String) : VM Unit :=
  modify fun st => { st with rep := { st.rep with faults := st.rep.faults.push s } }

private def addDecl (d : Declaration) : VM Bool := do
  let st ← get
  match st.env.addDeclCore 0 512 d none with
  | .ok env' =>
    set { st with env := env' }
    return true
  | .error e =>
    fault s!"kernel: {← kernelMsg e}"
    return false

private def union (a b : Array ByteArray) : Array ByteArray :=
  b.foldl (fun acc x => if acc.contains x then acc else acc.push x) a

/-- Add `name` (and what it needs) to the environment. Returns whether the
    name is now available. `refIdOf` is the citing declaration's view of
    names → ref ids, used to assume a missing name by its statement. -/
partial def visit (rebuilt : Std.HashMap Name Rebuilt) (stmts : Std.HashMap ByteArray (UnitData × Decoration))
    (table : FileTable) (name : Name) (refIdOf : Name → Option ByteArray) : VM Bool := do
  if let some r := (← get).done.get? name then return r
  -- Already in the environment (imports, or added as part of a block).
  if (← get).env.contains name then
    if let some rb := rebuilt.get? name then
      let ci := (← get).env.find? name |>.get!
      unless sameConstant ci rb.ci (binderNames := false) do
        fault s!"{name}: the file's declaration differs from the environment's"
      modify fun st => { st with rep := { st.rep with present := st.rep.present + 1 } }
    modify fun st => { st with done := st.done.insert name true, assumesOf := st.assumesOf.insert name #[] }
    return true
  let some rb := rebuilt.get? name
    | -- Not in the file: assume it by its statement, if the file has one.
      match refIdOf name >>= fun r => (stmts.get? r).map (r, ·) with
      | some (r, (u, de)) =>
        match rebuildStatement u table de with
        | .error e => fault s!"{name}: statement to assume does not rebuild: {e}"; markFail name; return false
        | .ok (lps, type) =>
          let mut ok := true
          for m in (CA.Util.collectConstants type).toList do
            unless ← visit rebuilt stmts table m (fun n => (deRef de u table).get? n) do ok := false
          unless ok do markFail name; return false
          let added ← addDecl (.axiomDecl { name, levelParams := lps, type, isUnsafe := false })
          unless added do markFail name; return false
          modify fun st => { st with
            done := st.done.insert name true, assumesOf := st.assumesOf.insert name #[r],
            assumedIds := st.assumedIds.insert name r,
            rep := { st.rep with assumed := st.rep.assumed.push (name, r) } }
          return true
      | none =>
        fault s!"{name}: not in the environment, not in the file, and no statement to assume{match refIdOf name with | some r => s!" (ref {b58 r})" | none => ""}"
        markFail name; return false
  if (← get).visiting.contains name then return true
  modify fun st => { st with visiting := st.visiting.insert name }
  -- Dependencies first. Siblings of a mutual definition (`all`) are not
  -- dependencies: safe mutual definitions are compiled to independent
  -- values; unsafe or partial ones are added together below.
  let siblings : List Name := match rb.ci with
    | .defnInfo v => v.all | .thmInfo v => v.all | .opaqueInfo v => v.all | _ => []
  let deps := (CA.RefHash.refsOf rb.ci true).toList.filter fun m => m != name && !siblings.contains m
  let mut ok := true
  let mut assumes : Array ByteArray := #[]
  for m in deps do
    -- Constructors and recursors are added with their inductive.
    if ← visit rebuilt stmts table m (rb.refIds.get? ·) then
      assumes := union assumes ((← get).assumesOf.getD m #[])
    else ok := false
  modify fun st => { st with visiting := st.visiting.erase name }
  unless ok do markFail name; return false
  if (← get).env.contains name then   -- added meanwhile, as part of a block
    modify fun st => { st with done := st.done.insert name true, assumesOf := st.assumesOf.insert name assumes }
    return true
  let finish (assumes : Array ByteArray) : VM Bool := do
    modify fun st => { st with done := st.done.insert name true, assumesOf := st.assumesOf.insert name assumes,
                               rep := { st.rep with added := st.rep.added + 1 } }
    return true
  match rb.ci with
  | .axiomInfo v => if ← addDecl (.axiomDecl v) then finish assumes else markFail name; return false
  | .defnInfo v =>
    if v.safety != .safe && v.all.length > 1 then
      -- Unsafe or partial mutual definitions reference each other: one declaration.
      let mut defs : Array DefinitionVal := #[]
      for s in v.all do
        match rebuilt.get? s with
        | some { ci := .defnInfo w, .. } => defs := defs.push w
        | _ => fault s!"{name}: mutual sibling {s} is not a definition in the file"; markFail name; return false
      if ← addDecl (.mutualDefnDecl defs.toList) then
        for s in v.all do
          modify fun st => { st with done := st.done.insert s true, assumesOf := st.assumesOf.insert s assumes,
                                     rep := { st.rep with added := st.rep.added + 1 } }
        return true
      else markFail name; return false
    else if ← addDecl (.defnDecl v) then finish assumes else markFail name; return false
  | .opaqueInfo v => if ← addDecl (.opaqueDecl v) then finish assumes else markFail name; return false
  | .thmInfo v =>
    if rb.statementOnly then
      -- Kept without its proof: an assumption of its own statement.
      if ← addDecl (.axiomDecl { name, levelParams := v.levelParams, type := v.type, isUnsafe := false }) then
        modify fun st => { st with assumedIds := st.assumedIds.insert name rb.stmt,
                                   rep := { st.rep with assumed := st.rep.assumed.push (name, rb.stmt) } }
        finish (union assumes #[rb.stmt])
      else markFail name; return false
    else if ← addDecl (.thmDecl v) then finish assumes else markFail name; return false
  | .quotInfo _ =>
    if ← addDecl .quotDecl then finish assumes else markFail name; return false
  | .ctorInfo v => visit rebuilt stmts table v.induct refIdOf
  | .recInfo v =>
    -- Produced by the kernel with its inductive family.
    match v.all.head? with
    | some ind =>
      if ← visit rebuilt stmts table ind refIdOf then
        if (← get).env.contains name then
          modify fun st => { st with done := st.done.insert name true, assumesOf := st.assumesOf.insert name assumes }
          return true
        else fault s!"{name}: the kernel produced no such recursor"; markFail name; return false
      else markFail name; return false
    | none => fault s!"{name}: recursor without a family"; markFail name; return false
  | .inductInfo v =>
    -- The whole family: every inductive in `all` with its constructors.
    let mut types : Array InductiveType := #[]
    let mut famAssumes := assumes
    for indName in v.all do
      let some ind := rebuilt.get? indName | fault s!"{name}: family member {indName} is not in the file"; markFail name; return false
      let .inductInfo iv := ind.ci | fault s!"{indName}: not an inductive"; markFail name; return false
      let mut ctors : Array Constructor := #[]
      for c in iv.ctors do
        let some cr := rebuilt.get? c | fault s!"{name}: constructor {c} is not in the file"; markFail name; return false
        -- The constructor's type references, outside the family.
        for m in (CA.Util.collectConstants cr.ci.type).toList do
          unless v.all.contains m do
            if ← visit rebuilt stmts table m (cr.refIds.get? ·) then
              famAssumes := union famAssumes ((← get).assumesOf.getD m #[])
            else ok := false
        ctors := ctors.push { name := c, type := cr.ci.type }
      for m in (CA.Util.collectConstants iv.type).toList do
        unless v.all.contains m do
          if ← visit rebuilt stmts table m (ind.refIds.get? ·) then
            famAssumes := union famAssumes ((← get).assumesOf.getD m #[])
          else ok := false
      types := types.push { name := indName, type := iv.type, ctors := ctors.toList }
    unless ok do markFail name; return false
    let added ← addDecl (.inductDecl v.levelParams v.numParams types.toList v.isUnsafe)
    unless added do markFail name; return false
    -- Mark the family, its constructors and its recursors; compare the
    -- recursors the kernel produced with the file's.
    let mut n := 0
    for indName in v.all do
      modify fun st => { st with done := st.done.insert indName true, assumesOf := st.assumesOf.insert indName famAssumes }
      n := n + 1
      if let some { ci := .inductInfo iv, .. } := rebuilt.get? indName then
        for c in iv.ctors do
          modify fun st => { st with done := st.done.insert c true, assumesOf := st.assumesOf.insert c famAssumes }
          n := n + 1
    let env := (← get).env
    for (rn, rr) in rebuilt.toArray do
      if let .recInfo rv := rr.ci then
        if rv.all.head? == v.all.head? then
          match env.find? rn with
          | some kci =>
            unless sameConstant kci rr.ci (binderNames := false) do
              fault s!"{rn}: the file's recursor differs from the kernel's"
            modify fun st => { st with rep := { st.rep with generated := st.rep.generated + 1 },
                                       done := st.done.insert rn true, assumesOf := st.assumesOf.insert rn famAssumes }
          | none => fault s!"{rn}: the kernel produced no such recursor"
    modify fun st => { st with rep := { st.rep with added := st.rep.added + n } }
    return true
where
  markFail (n : Name) : VM Unit := modify fun st => { st with done := st.done.insert n false }
  /-- Names → ref ids as a statement decoration sees them. -/
  deRef (de : Decoration) (u : UnitData) (table : FileTable) : Std.HashMap Name ByteArray := Id.run do
    let mut m := {}
    for j in [:u.refs.size] do
      match de.refNames[j]?, table.refs[u.refs[j]!]? with
      | some p, some r => if let some nm := table.names[p]? then m := m.insert nm r
      | _, _ => pure ()
    return m

/-- Verify every declaration of `node` against `env` (the imports the file
    was built on). Returns the extended environment and the report; one
    record per theorem the kernel accepted. -/
def verifyNode (env : Environment) (node : CA.Node.Node) (hasher : CA.SHA256.Hasher := CA.SHA256.pureHasher) :
    IO (Environment × Report) := do
  let (rebuilt, faults0) ← rebuildAll node hasher
  let stmts := statementsOf node
  let names := (rebuilt.toArray.map (·.1)).qsort Name.lt
  let act : VM Unit := do
    modify fun st => { st with rep := { st.rep with faults := faults0 } }
    for n in names do
      let rb := rebuilt.get! n
      discard <| visit rebuilt stmts node.table n (rb.refIds.get? ·)
    -- Records for the theorems the kernel accepted.
    let st ← get
    let assumedSet : Std.HashSet Name := st.assumedIds.fold (fun s n _ => s.insert n) {}
    let mut recs := #[]
    for n in names do
      let rb := rebuilt.get! n
      let .thmInfo _ := rb.ci | continue
      if rb.statementOnly then continue
      unless st.done.getD n false do continue
      unless st.env.contains n do continue
      let axs := (axiomsOf st.env n).toArray.filter (!assumedSet.contains ·)
      let valid := !axs.contains ``sorryAx
      let r : Record := {
        name := n, decl := rb.decl, stmt := rb.stmt,
        assumes := st.assumesOf.getD n #[], axioms := axs.qsort Name.lt, valid := valid }
      recs := recs.push r
    modify fun st => { st with rep := { st.rep with records := recs } }
  let ((), st) ← act.run { env }
  return (st.env, st.rep)

/-- The JSON a record is stored and signed as (`registry-protocol.md` §3). -/
def Record.toJson (r : Record) (toolchain : String) : Json :=
  Json.mkObj [
    ("decl", .str (b58 r.decl)), ("stmt", .str (b58 r.stmt)), ("name", .str r.name.toString),
    ("assumes", .arr (r.assumes.map (.str <| b58 ·))),
    ("axioms", .arr (r.axioms.map (.str ·.toString))),
    ("toolchain", .str toolchain), ("policy", .str "kernel"), ("valid", .bool r.valid)]

end CA.Verify

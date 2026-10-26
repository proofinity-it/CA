import Lean
import Lean.Elab.Frontend
import CA.Node

/-!
Test executable for `CA.Node.packDecls`: packing without an `Environment`.
Elaborates a small source against `Init` and packs its own declarations
twice:

* with `packEnvironment` (the cone walked in the environment);
* with `packDecls`, given only those declarations and the ids of what
  they reference, as a store holding declarations and ids would.

The two nodes must hold the same rows, byte for byte, and `checkNode`
must find no fault in either. A block packed with one member missing
must not reproduce the block's ids.
-/

open Lean CA.RefHash CA.Node

private def src : String := "
def f (n : Nat) : Nat := n + 1
theorem t1 : (1 : Nat) + 1 = 2 := rfl
theorem t2 : (1 : Nat) + 1 = 2 := by decide
mutual
  def ev : Nat → Bool
    | 0 => true
    | n+1 => od n
  def od : Nat → Bool
    | 0 => false
    | n+1 => ev n
end
inductive T where
  | a | b
structure P where
  x : Nat
  y : Nat
def P.swap (p : P) : P := ⟨p.2, p.1⟩
def g (t : T) (p : P) : Nat := match t with | .a => p.x + f p.y | .b => if ev p.x then 1 else 0
mutual
  inductive A where | leaf | node (b : B)
  inductive B where | wrap (a : A)
end
"

private unsafe def enableInitImpl : IO Unit := Lean.enableInitializersExecution
@[implemented_by enableInitImpl] private opaque enableInit : IO Unit

/-- The rows of a node as one comparable value. -/
private def rows (n : Node) : List String :=
  let b := CA.RefHash.toB58
  n.table.refs.toList.map b ++ n.table.names.toList.map toString ++
  n.units.toList.map (fun u => s!"{b u.key} {b u.variant} {u.form.byte} {b u.bytes}") ++
  n.members.toList.map (fun m => s!"{b m.decl} {m.name} {b m.key} {b m.variant} {m.member}") ++
  n.decorations.toList.map (fun d => s!"{b d.decl} {d.name} {b d.bytes}") ++
  n.declarations.toList.map (fun d => s!"{b d.decl} {d.kind} {b d.stmt} {b d.ref}") ++
  n.witnesses.toList.map (fun (s, d) => s!"{b s} {b d}") ++
  n.deps.toList.map (fun d => s!"{b d.decl} {b d.ref}")

/-! ## Random declarations for the codec property test -/

private def sigConsts : Array (Name × List Level) := #[(``Nat, []), (``Nat.add, []), (``Nat.zero, []),
  (``Nat.succ, []), (``Eq, [.succ .zero]), (``True, []), (``Prod, [.zero, .zero]), (``List, [.zero])]

private def binderNames : Array Name := #[`x, `y, `z, `h, `α]

private def rnd (n : Nat) : IO Nat := IO.rand 0 (n - 1)

/-- A random closed term (de Bruijn-valid under `bound` binders), depth-limited. -/
private partial def genExpr (depth bound : Nat) (lps : List Name) : IO Expr := do
  let leaf := depth == 0 || (← rnd 4) == 0
  if leaf then
    let k ← rnd (if bound > 0 then 5 else 4)
    match k with
    | 0 =>
      let (c, ls) := sigConsts[← rnd sigConsts.size]!
      return .const c ls
    | 1 =>
      if lps.isEmpty || (← rnd 2) == 0 then return .sort .zero
      let i ← rnd lps.length
      return .sort (.param lps[i]!)
    | 2 => return .lit (.natVal (← rnd 300))
    | 3 => return .lit (.strVal (if (← rnd 2) == 0 then "a" else "ø"))
    | _ => return .bvar (← rnd bound)
  else
    let k ← rnd 5
    let nm := binderNames[← rnd binderNames.size]!
    match k with
    | 0 => return .app (← genExpr (depth - 1) bound lps) (← genExpr (depth - 1) bound lps)
    | 1 =>
      let bi : BinderInfo := if (← rnd 2) == 0 then .default else .implicit
      return .lam nm (← genExpr (depth - 1) bound lps) (← genExpr (depth - 1) (bound + 1) lps) bi
    | 2 =>
      let bi : BinderInfo := if (← rnd 2) == 0 then .default else .instImplicit
      return .forallE nm (← genExpr (depth - 1) bound lps) (← genExpr (depth - 1) (bound + 1) lps) bi
    | 3 =>
      let nd := (← rnd 2) == 0
      return .letE nm (← genExpr (depth - 1) bound lps) (← genExpr (depth - 1) bound lps)
        (← genExpr (depth - 1) (bound + 1) lps) nd
    | _ => return .proj ``Prod (← rnd 2) (← genExpr (depth - 1) bound lps)

private def randomDecl (i : Nat) : IO (Name × ConstantInfo) := do
  let name := Name.mkSimple s!"rnd_{i}"
  let lps : List Name ← match ← rnd 3 with
    | 0 => pure [] | 1 => pure [`u] | _ => pure [`u, `v]
  let type ← genExpr 4 0 lps
  let cv : ConstantVal := { name, levelParams := lps, type }
  let kind ← rnd 4
  if kind == 0 then return (name, .axiomInfo { cv with isUnsafe := false })
  let value ← genExpr 4 0 lps
  if kind == 1 then
    let h ← rnd 3
    let hints : ReducibilityHints ← match h with
      | 0 => pure .opaque | 1 => pure .abbrev | _ => pure (.regular (← rnd 20).toUInt32)
    return (name, .defnInfo { cv with value, safety := .safe, all := [name], hints })
  if kind == 2 then return (name, .thmInfo { cv with value, all := [name] })
  return (name, .opaqueInfo { cv with value, isUnsafe := false, all := [name] })

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInit
  let some env ← Elab.runFrontend src {} "<node-test>" `NodeTest
    | throw (IO.userError "elaboration failed")
  let oursRef ← IO.mkRef (#[] : Array (Name × ConstantInfo))
  env.constants.map₂.forM fun n ci => oursRef.modify (·.push (n, ci))
  let ours := (← oursRef.get).qsort (·.1.lt ·.1)
  let roots := ours.map (·.1)
  let mut fails := 0

  let (a, repA) ← packEnvironment env roots (cacheDir := none)
  -- What a store holds: the ids of the dependencies, nothing else.
  let cone := coneOf env roots true
  let (_, full) ← computeIds cone
  let base : RefTable := roots.foldl (·.erase ·) full
  let (b, repB, ids) ← packDecls ours base
  IO.println s!"node-test: {roots.size} declarations, {b.units.size} units, base of {base.size} ids"
  if !repA.errors.isEmpty || !repB.errors.isEmpty then
    IO.println s!"  FAIL pack errors: {repA.errors} {repB.errors}"; fails := fails + 1
  if rows a == rows b then IO.println "  ok   packDecls rows = packEnvironment rows"
  else IO.println "  FAIL packDecls rows differ from packEnvironment rows"; fails := fails + 1
  if ids.all (·.unresolved.isEmpty) && repB.unresolved == 0 then IO.println "  ok   every id exact"
  else IO.println "  FAIL some ids hashed by name"; fails := fails + 1
  for (label, n) in [("packEnvironment", a), ("packDecls", b)] do
    let c ← checkNode n
    if c.faults.isEmpty && c.rebuilt > 0 && c.members == n.members.size then
      IO.println s!"  ok   checkNode {label}: {c.members} members, {c.rebuilt} rebuilt, no fault"
    else IO.println s!"  FAIL checkNode {label}: {c.faults}"; fails := fails + 1

  -- `od` without `ev`: the block's ids cannot come out the same, so
  -- nothing is packed and the missing member is named.
  let noEv := ours.filter (·.1 != `ev)
  let (n2, rep2, ids2) ← packDecls noEv base
  if ids2.isEmpty && n2.units.isEmpty && rep2.errors.any (·.endsWith "block member ev is not given") then
    IO.println "  ok   a block with a member missing is refused, the member named"
  else IO.println s!"  FAIL a missing block member went unnoticed: {rep2.errors}"; fails := fails + 1

  -- `A.rec` without `B.rec`: the recursors of a mutual family are one block.
  let noBrec := ours.filter (·.1 != `B.rec)
  let (n3, rep3, ids3) ← packDecls noBrec base
  if ids3.isEmpty && n3.units.isEmpty && rep3.errors.any (·.endsWith "block member B.rec is not given") then
    IO.println "  ok   a recursor packed without its mutual sibling recursor is refused"
  else IO.println s!"  FAIL A.rec without B.rec went unnoticed: {rep3.errors.toList.take 3}"; fails := fails + 1
  -- Remap: every unit re-encoded against a reversed ref table checks to the
  -- same key from the new table; decorations renumbered decode.
  let rev : CA.Payload.FileTable := (a.table.refs.reverse.foldl (fun t r => (t.refIx r).1) {})
  let rev := a.table.names.reverse.foldl (fun t n => (t.nameIx n).1) rev
  let mut remapOk := true
  let mut remapped := 0
  for u in a.units do
    match CA.Payload.decodeUnit u.bytes >>= fun d => CA.Payload.remapUnit d a.table rev with
    | .error _ => remapOk := false
    | .ok (d', _) =>
      if d'.toBytes == u.bytes && d'.refs.size > 1 then remapOk := false   -- positions must have moved
      match ← CA.Payload.checkUnit d' rev.refs with
      | .ok c => if c.key != u.key then remapOk := false else remapped := remapped + 1
      | .error _ => remapOk := false
  for d in a.decorations do
    match CA.Payload.decodeDecoration d.bytes >>= fun de => CA.Payload.remapDecoration de a.table rev with
    | .error _ => remapOk := false
    | .ok (de', _) => if (CA.Payload.decodeDecoration de'.toBytes).isOk != true then remapOk := false
  if remapOk && remapped == a.units.size then IO.println s!"  ok   {remapped} units remapped onto a reversed table keep their ids"
  else IO.println "  FAIL remap changed an id or failed"; fails := fails + 1
  -- Merge: a node with itself is the identity up to row order; with a
  -- node holding other declarations, the union.
  let (aa, errsAA) ← merge a a
  if errsAA.isEmpty && aa.units.size == a.units.size && aa.members.size == a.members.size &&
      aa.declarations.size == a.declarations.size && aa.decorations.size == a.decorations.size then
    IO.println "  ok   merge (a, a) = a up to row order"
  else IO.println s!"  FAIL merge (a, a): {errsAA} {aa.units.size}/{a.units.size}"; fails := fails + 1
  let (onlyA, onlyB, _, opened) ← diff a n2
  if onlyA.size == (contentKeys a).size && onlyB.isEmpty && opened > 0 then
    IO.println s!"  ok   diff against an empty node names every key through {opened} opened buckets"
  else IO.println "  FAIL diff"; fails := fails + 1

  -- deps rows: every one cites a reference of the member's unit.
  if !a.deps.isEmpty && (rows a == rows b) then
    IO.println s!"  ok   {a.deps.size} dependency rows, identical on both paths"
  else IO.println "  FAIL deps rows missing or differ"; fails := fails + 1

  -- Decoration vectors (payload.md §9): decoding the fixed bytes gives the fields.
  let unhex (h : String) : ByteArray := Id.run do
    let cs := h.toList.toArray
    let v (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
    let mut b := ByteArray.empty
    for i in [:cs.size / 2] do b := b.push (v cs[2*i]! * 16 + v cs[2*i+1]!).toUInt8
    return b
  let vectors : List (Name × Nat × Nat × List Name × List Name × Option ReducibilityHints × String) := [
    (`T, 1, 0, [], [], none, "010100015401000000ff"),
    (`T.a, 0, 0, [], [], none, "010200015400016100000000ff"),
    (`T.b, 2, 0, [], [], none, "010200015400016202000000ff"),
    (`T.rec, 0, 3, [`u], [`motive, `t, `a, `b], none, "0102000154000372656300030001020101000175040100066d6f74697665010001740100016101000162ff"),
    (`idT, 0, 1, [], [`x], some (.regular 1), "010100036964540001000001010001780201"),
    (`Conj, 0, 7, [], [`n], none, "01010004436f6e6a00070001020304050600010100016eff")]
  let mut vecOk := true
  for (own, member, slots, lps, binders, hints, hx) in vectors do
    match CA.Payload.decodeDecoration (unhex hx) with
    | .error e => IO.println s!"    {own}: {e}"; vecOk := false
    | .ok d =>
      let hintsEq := match d.hints, hints with
        | none, none => true | some .opaque, some .opaque => true | some .abbrev, some .abbrev => true
        | some (.regular a), some (.regular b) => a == b | _, _ => false
      unless d.own == own && d.member == member && d.refNames == (Array.range slots) &&
          d.levelParams.toList == lps && d.binders.toList == binders && hintsEq && d.toBytes == unhex hx do
        IO.println s!"    {own}: decoded {d.own} {d.member} {d.refNames} {d.levelParams} {d.binders}"; vecOk := false
  if vecOk then IO.println "  ok   6 decoration vectors decode to their fields and re-encode to the same bytes"
  else IO.println "  FAIL decoration vectors"; fails := fails + 1

  -- Property test (docs/plan.md item 4): random closed terms over a small
  -- signature, packed as axioms, definitions, theorems and opaques; every
  -- unit checks and every member rebuilds exactly.
  let sigCone := coneOf env (sigConsts.map (·.1)) true
  let (_, sigTable) ← computeIds sigCone
  let mut decls : Array (Name × ConstantInfo) := #[]
  for i in [:300] do
    decls := decls.push (← randomDecl i)
  let (rn, rrep, _) ← packDecls decls sigTable
  let rc ← checkNode rn
  let byName : Std.HashMap Name ConstantInfo := decls.foldl (fun m (n, ci) => m.insert n ci) {}
  let decoOf : Std.HashMap (ByteArray × Name) ByteArray :=
    rn.decorations.foldl (fun m r => m.insert (r.decl, r.name) r.bytes) {}
  -- Every declaration is standalone here, so each member row rebuilds alone
  -- (two random declarations with equal content are twins on one unit).
  let unitOf : Std.HashMap (ByteArray × ByteArray) UnitRow :=
    rn.units.foldl (fun m u => m.insert (u.key, u.variant) u) {}
  let mut rebuiltOk := 0
  for m in rn.members do
    let some u := unitOf.get? (m.key, m.variant) | continue
    let some d := (CA.Payload.decodeUnit u.bytes).toOption | continue
    let some b := decoOf.get? (m.decl, m.name) | continue
    let some de := (CA.Payload.decodeDecoration b).toOption | continue
    match CA.Payload.rebuild d rn.table #[de] with
    | .ok cis =>
      for (n, ci) in cis do
        if n == m.name && (byName.get? n).any (CA.Payload.sameConstant · ci) then rebuiltOk := rebuiltOk + 1
    | .error _ => pure ()
  if rrep.errors.isEmpty && rc.faults.isEmpty && rebuiltOk == 300 && rn.members.size == 300 then
    IO.println s!"  ok   300 random declarations: packed, checked without fault, all rebuilt exactly"
  else
    IO.println s!"  FAIL random declarations: errors {rrep.errors.toList.take 3}, faults {rc.faults.toList.take 3}, rebuilt {rebuiltOk}/300, units {rn.units.size}"
    fails := fails + 1

  IO.println (if fails == 0 then "node-test: all passed" else s!"node-test: {fails} FAILED")
  return if fails == 0 then 0 else 1

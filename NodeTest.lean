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
  n.witnesses.toList.map (fun (s, d) => s!"{b s} {b d}")

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

  IO.println (if fails == 0 then "node-test: all passed" else s!"node-test: {fails} FAILED")
  return if fails == 0 then 0 else 1

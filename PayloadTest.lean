import Lean
import Lean.Elab.Frontend
import CA.Payload

/-!
Test executable for `CA.Payload` (`docs/payload.md`). Elaborates a small
source against `Init`, computes ids for the whole environment, then for
every strongly connected component (standalone constant or block):

* encodes it as a unit with decorations, against one shared file table;
* checks the unit: the ids recomputed from its bytes alone equal the ids
  `CA.RefHash` gave the original declarations;
* decodes unit and decorations and re-serialises them: same bytes;
* rebuilds the `ConstantInfo`s and recomputes their ids: unchanged;
* requires every member to come back exactly (`Encoded.exact`), and
  counts keys that hold more than one unit (naming variants).

Plus targeted cases: a statement unit for `Nat.add_zero`'s type matches
`spec.md`'s golden `stmt`; statement mode; a tampered unit fails its
check; twins referenced together get two slots and come back exactly.
-/

open Lean CA.RefHash CA.Payload

private def src : String := "
def f (n : Nat) : Nat := n + 1
theorem t1 : (1 : Nat) + 1 = 2 := rfl
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
def big : Nat := 18446744073709551616
def withLet (n : Nat) : Nat := let m := n + 1; m * m
def u1.{u, v} : Type (max u v) := PUnit
theorem byDecide : 2 ^ 10 = 1024 := by decide
def A1 : Nat := 1
def A2 : Nat := 1
def useBoth : Nat := A1 + A2
"

private unsafe def enableInitImpl : IO Unit := Lean.enableInitializersExecution
@[implemented_by enableInitImpl] private opaque enableInit : IO Unit

private def b58 := CA.RefHash.toB58

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInit
  let some env ← Elab.runFrontend src {} "<payload-test>" `PayloadTest
    | throw (IO.userError "elaboration failed")
  let mut decls : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do decls := decls.push (n, ci)
  let oursRef ← IO.mkRef (#[] : Array (Name × ConstantInfo))
  env.constants.map₂.forM fun n ci => oursRef.modify (·.push (n, ci))
  decls := decls ++ (← oursRef.get)
  let byName : Std.HashMap Name ConstantInfo := decls.foldl (fun m (n, ci) => m.insert n ci) {}
  IO.println s!"payload-test: {decls.size} constants"
  let t0 ← IO.monoMsNow
  let (ids, table) ← computeIds decls
  IO.println s!"  ids in {(← IO.monoMsNow) - t0} ms"

  -- Components: blocks grouped by block id, everything else alone.
  let mut groups : Std.HashMap ByteArray (Array Name) := {}
  let mut singles : Array Name := #[]
  for d in ids do
    match d.block with
    | some (b, _) => groups := groups.insert b ((groups.getD b #[]).push d.name)
    | none => singles := singles.push d.name
  let idsOf : Std.HashMap Name DeclIds := ids.foldl (fun m d => m.insert d.name d) {}
  -- Twin blocks share a block id, so a group may hold several SCCs.
  let mut blocks : Array (Array Name) := #[]
  for (_, g) in groups.toArray do
    let succ (n : Name) : Array Name := (refsOf (byName.get! n)).toArray
    blocks := blocks ++ sccs g succ
  let comps : Array (Array Name) := singles.map (#[·]) ++ blocks
  IO.println s!"  {comps.size} components ({blocks.size} blocks, {groups.size} block ids)"

  let mut ft : FileTable := {}
  let mut fails := 0
  let mut inexact : Array Name := #[]
  let mut binderOnly := 0
  let mut otherInexact : Array Name := #[]
  let mut otherCount := 0
  let mut unitsWithCollisions := 0
  let mut byKey : Std.HashMap ByteArray (Array ByteArray) := {}
  let mut collisionKinds : Std.HashMap String Nat := {}
  let mut collisionSample : Array (Name × Name) := #[]
  let mut unitBytes := 0
  let mut decoBytes := 0
  let mut nUnits := 0
  let report (msg : String) : IO Unit := IO.println s!"  FAIL {msg}"
  let t1 ← IO.monoMsNow
  for comp in comps do
    let input := comp.map fun n => (n, byName.get! n)
    match ← encodeUnit input table ft with
    | .error e => fails := fails + 1; report s!"encode {comp[0]!}: {e}"
    | .ok (enc, ft') =>
      ft := ft'
      nUnits := nUnits + 1
      unitBytes := unitBytes + enc.bytes.size
      for (_, d) in enc.decorations do decoBytes := decoBytes + d.size
      let seen := byKey.getD enc.key #[]
      if !seen.contains enc.bytes then byKey := byKey.insert enc.key (seen.push enc.bytes)
      if !enc.collisions.isEmpty then
        unitsWithCollisions := unitsWithCollisions + 1
        for (a, b) in enc.collisions do
          let k := s!"{CA.Util.constantKind (byName.getD a (.axiomInfo default))}"
          collisionKinds := collisionKinds.insert k (collisionKinds.getD k 0 + 1)
          if collisionSample.size < 20 then collisionSample := collisionSample.push (a, b)
      if !enc.exact then
        inexact := inexact ++ enc.inexact
        -- classify: does it come back up to binder names?
        match decodeUnit enc.bytes with
        | .ok u =>
          let ds := enc.decorations.filterMap fun (_, b) => (decodeDecoration b).toOption
          match rebuild u ft ds with
          | .ok back =>
            for (n, ci) in back do
              if enc.inexact.contains n then
                if sameConstant (byName.get! n) ci (binderNames := false) then
                  binderOnly := binderOnly + 1
                else if otherInexact.size < 15 then otherInexact := otherInexact.push n
                else otherCount := otherCount + 1
          | .error _ => pure ()
        | .error _ => pure ()
      -- 1. The unit's bytes alone give the original ids.
      match decodeUnit enc.bytes with
      | .error e => fails := fails + 1; report s!"decode {comp[0]!}: {e}"
      | .ok u =>
        if u.toBytes != enc.bytes then
          fails := fails + 1; report s!"re-serialise {comp[0]!}"
        match ← checkUnit u ft.refs with
        | .error e =>
          fails := fails + 1; report s!"check {comp[0]!}: {e}"
          if fails ≤ 2 then
            for d in enc.ids do
              IO.println s!"      unit order: {d.name} ({CA.Util.constantKind (byName.get! d.name)})"
        | .ok c =>
          if c.key != enc.key then fails := fails + 1; report s!"key {comp[0]!}"
          for i in [:enc.ids.size] do
            let want := idsOf.get! enc.ids[i]!.name
            let (s, d, r) := c.ids[i]!
            if s != want.stmt || d != want.decl || r != want.ref then
              fails := fails + 1; report s!"ids {want.name}"
        -- 2. Decorations re-serialise and rebuild declarations with the same ids.
        let mut decos := #[]
        for (n, bytes) in enc.decorations do
          match decodeDecoration bytes with
          | .error e => fails := fails + 1; report s!"decoration {n}: {e}"
          | .ok d =>
            if d.toBytes != bytes then fails := fails + 1; report s!"decoration bytes {n}"
            decos := decos.push d
        match rebuild u ft decos with
        | .error e => fails := fails + 1; report s!"rebuild {comp[0]!}: {e}"
        | .ok back =>
          let (again, _) ← computeIds back table
          for d in again do
            let want := idsOf.get! d.name
            if d.stmt != want.stmt || d.decl != want.decl || d.ref != want.ref then
              fails := fails + 1; report s!"rebuilt ids {d.name}"
  let t2 ← IO.monoMsNow
  IO.println s!"  {nUnits} units in {t2 - t1} ms: units {unitBytes} B, decorations {decoBytes} B, file table {ft.refs.size} refs / {ft.names.size} names"
  IO.println s!"  inexact members: {inexact.size}: binder names only {binderOnly}, other {otherInexact.size + otherCount}"
  let variants := byKey.fold (fun n _ v => if v.size > 1 then n + 1 else n) 0
  IO.println s!"  distinct keys {byKey.size}; keys with more than one unit (naming variants): {variants}"
  if inexact.size > 0 then fails := fails + 1
  IO.println s!"  units with two names on one reference: {unitsWithCollisions}; by kind of the referenced constant: {collisionKinds.toList}"
  for (a, b) in collisionSample do IO.println s!"    {a}  ≡  {b}"
  for n in inexact.toList.take 10 do IO.println s!"    {n}"

  -- 3. Statement unit: Nat.add_zero's type gives spec.md's golden stmt.
  let golden := "ByKFv4nqHrcsFWuBFd7ihUXKFNEdMvFdMvjW7n8XE3nn"
  let az := byName.get! `Nat.add_zero
  match ← encodeStatement az.levelParams az.type table ft with
  | .error e => fails := fails + 1; report s!"statement: {e}"
  | .ok (enc, ft') =>
    match decodeUnit enc.bytes with
    | .error e => fails := fails + 1; report s!"statement decode: {e}"
    | .ok u =>
      match ← checkUnit u ft'.refs with
      | .ok c =>
        let ok := b58 c.key == golden && b58 c.key == b58 (idsOf.get! `Nat.add_zero).stmt
        IO.println s!"  statement unit for Nat.add_zero: {b58 c.key} {if ok then "= golden" else "MISMATCH"} ({enc.bytes.size} B)"
        if !ok then fails := fails + 1
      | .error e => fails := fails + 1; report s!"statement check: {e}"

  -- 4. Statement mode: a theorem without its proof keeps stmt and ref.
  match ← encodeUnit #[(`byDecide, byName.get! `byDecide)] table ft (withProofs := false) with
  | .error e => fails := fails + 1; report s!"statement mode: {e}"
  | .ok (enc, ft') =>
    match decodeUnit enc.bytes with
    | .ok u =>
      match ← checkUnit u ft'.refs with
      | .ok c =>
        let want := idsOf.get! `byDecide
        let (s, _, r) := c.ids[0]!
        let ok := s == want.stmt && r == want.ref
        IO.println s!"  statement mode (byDecide): {if ok then "stmt and ref kept" else "MISMATCH"}; {enc.bytes.size} B without the proof"
        if !ok then fails := fails + 1
      | .error e => fails := fails + 1; report s!"statement mode check: {e}"
    | .error e => fails := fails + 1; report s!"statement mode decode: {e}"

  -- 5. Tampering: change one node and the check must not reproduce the key.
  match ← encodeUnit #[(`f, byName.get! `f)] table ft with
  | .ok (enc, ft') =>
    match decodeUnit enc.bytes with
    | .ok u =>
      let nodes := u.nodes.map fun n => match n with
        | .natLit 1 => Node.natLit 2
        | n => n
      match ← checkUnit { u with nodes } ft'.refs with
      | .ok c =>
        let ok := c.key != enc.key
        IO.println s!"  tampered unit (f, 1 ↦ 2): {if ok then "key differs" else "SAME KEY"}"
        if !ok then fails := fails + 1
      | .error _ => IO.println "  tampered unit (f, 1 ↦ 2): rejected"
    | .error e => fails := fails + 1; report s!"tamper decode: {e}"
  | .error e => fails := fails + 1; report s!"tamper encode: {e}"

  -- 6. Twins referenced together: A1 and A2 share an id, so useBoth's unit
  --    gives them two slots for one id, and both names come back.
  match ← encodeUnit #[(`useBoth, byName.get! `useBoth)] table ft with
  | .ok (enc, _) =>
    let ok := enc.exact && !enc.collisions.isEmpty
    IO.println s!"  twins referenced together (useBoth): {if ok then "two slots for one id, rebuilt exactly" else "WRONG"}"
    if !ok then fails := fails + 1
  | .error e => fails := fails + 1; report s!"twins: {e}"

  IO.println (if fails == 0 then "all passed" else s!"{fails} failed")
  return if fails == 0 then 0 else 1

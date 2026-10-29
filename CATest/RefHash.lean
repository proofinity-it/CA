import Lean
import Lean.Elab.Frontend
import CA.RefHash

/-!
Test executable for `CA.RefHash`. Elaborates a small source string against
`Init`, computes ids with the whole of `Init` as the base table, and
checks the semantic properties the scheme promises:

* names never enter an id (α-renamed declarations get equal ids);
* theorems: equal statements ⇒ equal `stmt`/`ref`, different proofs ⇒
  different `decl`;
* definitions: equal types but different values ⇒ equal `stmt`, different
  `decl`/`ref` — and a statement *about* them differs accordingly;
* mutual / inductive blocks: members share a block id, get distinct
  member indices, and the whole thing is deterministic across runs;
* universe binder *order* is part of the identity (use sites instantiate
  levels positionally), while binder *names* are not;
* with a complete base table nothing is unresolved — and with an
  incomplete one, `unresolved` is complete even for subterms that hit
  the cross-declaration shared memo;
* `Nat` literals are hashed at full precision (`2^64` ≠ `0`);
* definitionally equal universe levels (`max u v` / `max v u`, `max u u` /
  `u`) give equal ids;
* golden ids: declarations that reference nothing outside their own
  block (`T`, `T.a`, `T.rec`, `idT`) have fixed, toolchain-independent
  ids — any change to the encoding scheme shows up here and must come
  with a `CA.schemeVersion` bump;
* `stmtIdOf` of a `def P : Prop := S`'s value equals the `stmt` of a
  theorem `: S` (the registry's open-point matching);
* `computeIds (withProofs := false)` gives the same `stmt` and `ref` for
  every declaration as the full computation;
* `sha256Pure` matches the FIPS 180-4 test vector (the cross-check
  against OpenSSL lives in the CLI: `ca selftest`).
-/

open Lean CA.RefHash

private def src : String := "
def A : Type := Nat
def B : Type := Bool
def f (n : Nat) : Nat := n + 1
def g (n : Nat) : Nat := n + 1
def h (n : Nat) : Nat := n + 2
theorem t1 : (1 : Nat) + 1 = 2 := rfl
theorem t2 : (1 : Nat) + 1 = 2 := by decide
theorem uses_f : f 0 = 1 := rfl
theorem uses_g : g 0 = 1 := rfl
theorem uses_h : h 0 = 2 := rfl
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
inductive T2 where
  | a | b
def q1.{u,v} : PProd PUnit.{u} PUnit.{v} := ⟨PUnit.unit, PUnit.unit⟩
def q2.{u,v} : PProd PUnit.{v} PUnit.{u} := ⟨PUnit.unit, PUnit.unit⟩
def q3.{a,b} : PProd PUnit.{a} PUnit.{b} := ⟨PUnit.unit, PUnit.unit⟩
theorem w1 : (1+2*3+4 = 11) ∧ ((1+2*3+4 = 11) ∧ (1+2*3+4 = 11)) := ⟨rfl, rfl, rfl⟩
theorem w2 : (1+2*3+4 = 11) ∧ (1+2*3+4 = 11) := ⟨rfl, rfl⟩
def big : Nat := 18446744073709551616
def zero : Nat := 0
def big5 : Nat := 18446744073709551621
def five : Nat := 5
def l1.{u,v} : Type (max u v) := PUnit
def l2.{u,v} : Type (max v u) := PUnit
def l3.{u} : Type (max u u) := PUnit
def l4.{u} : Type u := PUnit
def idT (x : T) : T := x
def PStmt : Prop := ∀ n : Nat, n + 0 = n
theorem pLit : ∀ n : Nat, n + 0 = n := fun n => Nat.add_zero n
"

private unsafe def enableInitImpl : IO Unit := Lean.enableInitializersExecution
@[implemented_by enableInitImpl] private opaque enableInit : IO Unit

private def elabSource (source : String) : IO Environment := do
  enableInit
  let some env ← Elab.runFrontend source {} "<refhash-test>" `RefHashTest
    | throw (IO.userError "elaboration failed")
  return env

private def b58 := CA.RefHash.toB58

def main : IO UInt32 := do
  IO.println "refhash-test: init search path"; (← IO.getStdout).flush
  initSearchPath (← findSysroot)
  IO.println "refhash-test: elaborating source"; (← IO.getStdout).flush
  let env ← elabSource src
  IO.println "refhash-test: elaborated"; (← IO.getStdout).flush

  -- Base table: every constant already in the environment before ours
  -- (i.e. Init), computed foundations-first. Also a rough perf probe.
  let mut baseDecls : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do
    baseDecls := baseDecls.push (n, ci)
  IO.println s!"Base: {baseDecls.size} Init constants"
  let t0 ← IO.monoMsNow
  let (baseIds, base) ← computeIds baseDecls
  let t1 ← IO.monoMsNow
  let unresolvedBase := baseIds.foldl (fun n d => n + d.unresolved.size) 0
  IO.println s!"  ids computed in {t1 - t0} ms; unresolved refs (total): {unresolvedBase}"
  let mut shown := 0
  for d in baseIds do
    if !d.unresolved.isEmpty && shown < 8 then
      IO.println s!"    {d.name} → unresolved {d.unresolved.toList.take 4}"
      shown := shown + 1

  -- Our declarations.
  let oursRef ← IO.mkRef (#[] : Array (Name × ConstantInfo))
  env.constants.map₂.forM fun n ci => do
    oursRef.modify (·.push (n, ci))
  let ours ← oursRef.get
  let (ids, _) ← computeIds ours base
  let byName : Std.HashMap Name DeclIds := ids.foldl (fun m d => m.insert d.name d) {}
  let get (n : Name) : IO DeclIds := do
    match byName.get? n with
    | some d => pure d
    | none => throw (IO.userError s!"missing ids for {n}")

  let check (label : String) (ok : Bool) : IO Unit := do
    if ok then IO.println s!"  ✓ {label}"
    else IO.println s!"  ✗ {label}"
  let mut fails : Array String := #[]
  let check (label : String) (ok : Bool) : IO (Array String) := do
    check label ok
    return if ok then #[] else #[label]

  IO.println "Properties:"
  let A ← get `A; let B ← get `B
  let f ← get `f; let g ← get `g; let h ← get `h
  let t1' ← get `t1; let t2' ← get `t2
  let uf ← get `uses_f; let ug ← get `uses_g; let uh ← get `uses_h
  let ev ← get `ev; let od ← get `od
  let T ← get `T; let Ta ← get `T.a; let Tb ← get `T.b; let Trec ← get `T.rec
  let T2 ← get `T2

  fails := fails ++ (← check "no unresolved references with a complete base"
    (ids.all (·.unresolved.isEmpty)))
  fails := fails ++ (← check "A, B : Type share a statement id" (A.stmt == B.stmt))
  fails := fails ++ (← check "A, B : Type have different decl ids" (A.decl != B.decl))
  fails := fails ++ (← check "f, g (α-renamed) have equal decl ids — names never enter"
    (f.decl == g.decl && f.ref == g.ref))
  fails := fails ++ (← check "f, h: same type ⇒ same stmt" (f.stmt == h.stmt))
  fails := fails ++ (← check "f, h: different value ⇒ different decl and ref"
    (f.decl != h.decl && f.ref != h.ref))
  fails := fails ++ (← check "t1, t2: same statement ⇒ same stmt and ref (proof irrelevance)"
    (t1'.stmt == t2'.stmt && t1'.ref == t2'.ref))
  fails := fails ++ (← check "t1, t2: different proofs ⇒ different decl" (t1'.decl != t2'.decl))
  fails := fails ++ (← check "uses_f, uses_g: statements about equal content are equal"
    (uf.stmt == ug.stmt))
  fails := fails ++ (← check "uses_f, uses_h: statements about different content differ"
    (uf.stmt != uh.stmt))
  fails := fails ++ (← check "ordinary defs and theorems are standalone (no block)"
    (f.block.isNone && t1'.block.isNone && A.block.isNone))
  fails := fails ++ (← check "ev, od form one block with distinct indices"
    (match ev.block, od.block with
     | some (b1, i1), some (b2, i2) => b1 == b2 && i1 != i2
     | _, _ => false))
  fails := fails ++ (← check "T, T.a, T.b form one block (the SCC); T.rec is a downstream node"
    (match T.block, Ta.block, Tb.block with
     | some (b, _), some (b1, _), some (b2, _) => b == b1 && b1 == b2 && Trec.block.isNone
     | _, _, _ => false))
  fails := fails ++ (← check "T, T2 (α-renamed inductives) have equal decl ids" (T.decl == T2.decl))
  fails := fails ++ (← check "T.a ≠ T.b" (Ta.decl != Tb.decl))

  -- Universe binder list: order is identity, names are not.
  let q1' ← get `q1; let q2' ← get `q2; let q3' ← get `q3
  fails := fails ++ (← check "q1, q3 (universe binders renamed) have equal ids"
    (q1'.stmt == q3'.stmt && q1'.decl == q3'.decl))
  fails := fails ++ (← check "q1, q2 (universe binders permuted) differ — instantiation is positional"
    (q1'.stmt != q2'.stmt && q1'.decl != q2'.decl))

  -- Nat literals: full precision (scheme 0 truncated to 64 bits).
  let big ← get `big; let zero ← get `zero; let big5 ← get `big5; let five ← get `five
  fails := fails ++ (← check "2^64 and 0 as literals have different ids" (big.decl != zero.decl))
  fails := fails ++ (← check "2^64+5 and 5 as literals have different ids" (big5.decl != five.decl))

  -- Universe levels: definitionally equal levels hash alike.
  let l1' ← get `l1; let l2' ← get `l2; let l3' ← get `l3; let l4' ← get `l4
  fails := fails ++ (← check "Type (max u v) and Type (max v u) have equal ids"
    (l1'.stmt == l2'.stmt && l1'.decl == l2'.decl))
  fails := fails ++ (← check "Type (max u u) and Type u have equal ids"
    (l3'.stmt == l4'.stmt && l3'.decl == l4'.decl))

  -- Golden ids (scheme version {CA.schemeVersion}): these declarations reference
  -- nothing outside their own block, so their ids depend only on the
  -- encoding scheme, not on the toolchain. Update together with a
  -- `CA.schemeVersion` bump, never silently.
  let idT' ← get `idT
  let golden : List (String × ByteArray × String) := [
    ("T.decl",     T.decl,     "AwbguQQn99uqMeaCaqyKHw57myYCFN8QxPuucQ8xeZTJ"),
    ("T.a.decl",   Ta.decl,    "39W2PKpM7xCyj9RyTYDNjnibqnAuCUqBJxgewcAvjYQK"),
    ("T.rec.stmt", Trec.stmt,  "6cqensD4yYH2bdFVSE3GAzBGexXV2M5NHCLiV4DjfAYD"),
    ("idT.decl",   idT'.decl,  "2L8HHtdHc1GnBSmsACbRew9etEWEo1y4ZnNhX8XjGn1N")]
  for (label, got, want) in golden do
    fails := fails ++ (← check s!"golden {label} = {want}" (b58 got == want))
    if b58 got != want then IO.println s!"      got {b58 got}"

  -- Unresolved reporting must survive the shared memo: with an empty base
  -- every Init reference is a by-name fallback, and w2's whole type is a
  -- subterm of w1's — a shared-memo hit must not hide w2's fallbacks.
  let pick (ns : List Name) : Array (Name × ConstantInfo) :=
    ns.foldl (fun a n => match ours.find? (·.1 == n) with
      | some p => a.push p | none => a) #[]
  let (wIds, _) ← computeIds (pick [`w1, `w2]) {}
  let wOk := wIds.size == 2 &&
    wIds.all (fun d => d.unresolved.contains `Nat && d.unresolved.contains `HMul.hMul)
  fails := fails ++ (← check "unresolved is complete across shared-memo hits (w1, w2)" wOk)

  -- Determinism: recompute and compare every id.
  let (ids2, _) ← computeIds ours base
  let same := ids.size == ids2.size &&
    (ids.zip ids2).all fun (a, b) => a.name == b.name && a.stmt == b.stmt && a.decl == b.decl && a.ref == b.ref
  fails := fails ++ (← check "deterministic across runs" same)

  -- Order independence: reversed input yields the same ids.
  let (ids3, _) ← computeIds ours.reverse base
  let m3 : Std.HashMap Name DeclIds := ids3.foldl (fun m d => m.insert d.name d) {}
  let sameOrder := ids.all fun d => match m3.get? d.name with
    | some d3 => d3.stmt == d.stmt && d3.decl == d.decl
    | none => false
  fails := fails ++ (← check "input order does not matter" sameOrder)

  -- An open point's statement id is the stmt of a theorem stating it.
  let pStmt ← get `PStmt; let pLit' ← get `pLit
  let pValue := match env.find? `PStmt with
    | some (.defnInfo v) => some (v.levelParams, v.value)
    | _ => none
  let stmtOfValue ← match pValue with
    | some (lp, v) => do let (h, u) ← stmtIdOf lp v base; pure (some (h, u))
    | none => pure none
  fails := fails ++ (← check "stmtIdOf (value of PStmt) = stmt of pLit, nothing unresolved"
    (match stmtOfValue with
     | some (h, u) => h == pLit'.stmt && u.isEmpty && h != pStmt.stmt
     | none => false))

  -- Proof-free mode: same stmt and ref everywhere, smaller cone.
  let (idsNP, _) ← computeIds ours base (withProofs := false)
  let mNP : Std.HashMap Name DeclIds := idsNP.foldl (fun m d => m.insert d.name d) {}
  let sameNP := ids.all fun d => match mNP.get? d.name with
    | some d' => d'.stmt == d.stmt && d'.ref == d.ref && d'.unresolved.isEmpty
    | none => false
  fails := fails ++ (← check "withProofs := false preserves stmt and ref of every declaration" sameNP)
  fails := fails ++ (← check "withProofs := false changes decl of theorems only"
    (ids.all fun d => match mNP.get? d.name, env.find? d.name with
      | some d', some (.thmInfo _) => d'.decl != d.decl
      | some d', some _ => d'.decl == d.decl
      | _, _ => false))

  -- Name-based type_hash (scheme 2): names are the leaves, cost is the DAG's.
  let th (n : Name) : IO ByteArray := do
    match env.find? n with
    | some ci => typeHashOf ci.levelParams ci.type
    | none => throw (IO.userError s!"missing {n}")
  fails := fails ++ (← check "type_hash: f, h (same type, by name) are equal"
    ((← th `f) == (← th `h)))
  fails := fails ++ (← check "type_hash: uses_f, uses_g differ — names are the leaves (stmt agrees)"
    ((← th `uses_f) != (← th `uses_g)))
  fails := fails ++ (← check "type_hash: q1, q3 equal, q1, q2 differ (positional universes)"
    ((← th `q1) == (← th `q3) && (← th `q1) != (← th `q2)))
  fails := fails ++ (← check "type_hash: Type (max u v) and Type (max v u) are equal"
    ((← th `l1) == (← th `l2)))
  fails := fails ++ (← check "type_hash ≠ stmt of the same declaration (domain separation)"
    ((← th `t1) != t1'.stmt))
  -- Names are encoded by component: `a.b` and «a.b» are different leaves.
  let dotted := mkConst (Name.mkStr .anonymous "a.b")
  fails := fails ++ (← check "type_hash: `a.b and «a.b» differ (names encoded by component)"
    ((← typeHashOf [] (mkConst `a.b)) != (← typeHashOf [] dotted)))
  -- A statement whose tree has 2^64 nodes and whose DAG has 66: `Eq ℕ e e`
  -- with e₀ = `Nat.zero`, eₖ₊₁ = `Nat.add eₖ eₖ`. Scheme 1 would expand
  -- the tree; scheme 2 must finish at once.
  let deep := (List.range 64).foldl (fun e _ => mkApp2 (mkConst ``Nat.add) e e) (mkConst ``Nat.zero)
  let tD0 ← IO.monoMsNow
  let hDeep ← typeHashOf [] (mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Nat) deep deep)
  let tD1 ← IO.monoMsNow
  fails := fails ++ (← check s!"type_hash of a 2^64-node tree (66-node DAG) in {tD1 - tD0} ms"
    (tD1 - tD0 < 2000 && hDeep.size == 32))
  -- A batch with one shared memo gives what single calls give.
  let batch ← typeHashes ours
  let singles ← ours.mapM fun (n, ci) => do return (n, ← typeHashOf ci.levelParams ci.type)
  fails := fails ++ (← check "typeHashes (shared memo) = typeHashOf one by one"
    (batch.size == singles.size && (batch.zip singles).all fun ((a, x), (b, y)) => a == b && x == y))
  -- Golden: built from bare constants, so no elaboration and no toolchain
  -- enters. Update only together with a `typeHashScheme` bump.
  let goldenTH := CA.SHA256.toHex256 hDeep
  let wantTH := "dda12a826db3b1b9a25cfc80c0fca6ef9fc272f925ae4907ff289c026bd9b3a1"
  fails := fails ++ (← check s!"golden type_hash of the deep Eq = {wantTH}" (goldenTH == wantTH))
  if goldenTH != wantTH then IO.println s!"      got {goldenTH}"

  -- Pure SHA-256 against the FIPS vector.
  let abcHex := CA.SHA256.toHex256 (CA.SHA256.sha256Pure "abc".toUTF8)
  fails := fails ++ (← check "sha256Pure(\"abc\") matches the FIPS vector"
    (abcHex == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"))

  IO.println ""
  IO.println s!"  f     stmt={b58 f.stmt}"
  IO.println s!"  f     decl={b58 f.decl}"
  IO.println s!"  t1    stmt={b58 t1'.stmt}  decl={b58 t1'.decl}"
  IO.println s!"  t2    stmt={b58 t2'.stmt}  decl={b58 t2'.decl}"
  IO.println s!"  ev    block={(ev.block.map fun (b, i) => s!"{b58 b}#{i}").getD "-"}"
  IO.println s!"  od    block={(od.block.map fun (b, i) => s!"{b58 b}#{i}").getD "-"}"

  let failures := fails.size
  if failures == 0 then
    IO.println "\nAll RefHash tests passed."
    return 0
  else
    IO.println s!"\n{failures} RefHash test(s) FAILED: {fails}"
    return 1

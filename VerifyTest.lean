import Lean
import Lean.Elab.Frontend
import CA.Node
import CA.Verify
import CA.SHA512
import CA.Ed25519

/-!
Test executable for `CA.Verify`: the kernel's verdict on a node.

* A small module is elaborated and packed (`packEnvironment`, proofs
  included); the node is verified against a fresh `Init` environment:
  every declaration is rebuilt and accepted by the kernel, the inductive
  family's recursors come out as the kernel's, and each theorem gets a
  record with no assumptions and only Lean's axioms.
* The same module packed in statement mode: theorems become assumptions
  of their own statement; nothing is proved.
* A forged node: a unit whose bytes encode a theorem with a wrong proof
  (`(2 : Nat) = 3 := Eq.refl 2`). Its ids are honest, so `checkNode`
  finds no fault; the kernel rejects it and no record is written.
* A theorem whose proof uses `sorry` gets an invalid record.
* A theorem citing a theorem that is not in the file but whose statement
  unit is (a registry entry) gets a record assuming that statement.
-/

open Lean CA.RefHash CA.Node CA.Verify

private def src : String := "
import CA
def f (n : Nat) : Nat := n + 1
theorem t1 : (1 : Nat) + 1 = 2 := rfl
@[publish] theorem t2 (n : Nat) : f n = n + 1 := rfl
theorem t3 : f 1 = 2 := t2 1
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
theorem swap_swap (p : P) : p.swap.swap = p := rfl
mutual
  inductive A where | leaf | node (b : B)
  inductive B where | wrap (a : A)
end
theorem with_sorry : (1 : Nat) = 1 := sorry
@[open_point] def Open1 : Prop := ∀ n : Nat, n * 1 = n
@[publish] theorem uses_open (h : Open1) : 2 * 1 = 2 := h 2
"

private unsafe def enableInitImpl : IO Unit := Lean.enableInitializersExecution
@[implemented_by enableInitImpl] private opaque enableInit : IO Unit

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInit
  let some env ← Elab.runFrontend src {} "<verify-test>" `VerifyTest
    | throw (IO.userError "elaboration failed")
  let base ← importModules #[{ module := `Init }] {}
  let own := (env.constants.map₂.toList.toArray.map (·.1)).qsort Name.lt
  let failsRef ← IO.mkRef (0 : Nat)
  let check (label : String) (ok : Bool) : IO Unit := do
    IO.println s!"  {if ok then "ok  " else "FAIL"} {label}"
    if !ok then failsRef.modify (· + 1)

  -- 1. Proofs included.
  let (node, prep) ← packEnvironment env own true (cacheDir := none)
  let (_, rep) ← verifyNode base node
  for f in rep.faults do IO.println s!"    fault: {f}"
  let ok1 := prep.errors.isEmpty && rep.faults.isEmpty && rep.added > 0 && rep.generated ≥ 3
  check s!"full node verifies: {rep.added} added, {rep.generated} recursors from the kernel, {rep.present} present, no fault" ok1
  let recOf (n : Name) := rep.records.find? (·.name == n)
  let ok2 := match recOf `t1, recOf `swap_swap with
    | some r, some s => r.valid && s.valid && r.assumes.isEmpty && s.assumes.isEmpty && r.axioms.isEmpty
    | _, _ => false
  check "t1 and swap_swap: valid records, nothing assumed, no axioms" ok2
  let ok3 := match recOf `with_sorry with
    | some r => !r.valid && r.axioms.contains ``sorryAx
    | none => false
  check "with_sorry: an invalid record naming sorryAx" ok3
  -- uses_open : Open1 → … : Open1 is a definition in the file, so nothing is assumed.
  let ok4 := match recOf `uses_open with
    | some r => r.valid && r.assumes.isEmpty
    | none => false
  check "uses_open: Open1 is a definition in the file, so the record assumes nothing" ok4

  -- 2. Statement mode: theorems are assumptions of their statements.
  let (nodeS, _) ← packEnvironment env own false (cacheDir := none)
  let (_, repS) ← verifyNode base nodeS
  let okS := repS.faults.isEmpty && repS.records.isEmpty &&
    repS.assumed.any (·.1 == `t1) && repS.assumed.any (·.1 == `swap_swap)
  check s!"statement mode: {repS.assumed.size} theorems assumed, no record, no fault" okS

  -- 3. A forged proof: honest ids, kernel rejection.
  let two := mkNatLit 2
  let three := mkNatLit 3
  let eqNat (a b : Expr) := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) a b
  let bad : ConstantInfo := .thmInfo {
    name := `bad, levelParams := [], type := eqNat two three,
    value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) two, all := [`bad] }
  let cone := coneOf base #[``Eq, ``Nat, ``Eq.refl] true
  let (_, table) ← computeIds cone
  let (forged, frep, _) ← packDecls #[(`bad, bad)] table
  let c ← checkNode forged
  let (_, repF) ← verifyNode base forged
  let okF := frep.errors.isEmpty && c.faults.isEmpty && repF.records.isEmpty &&
    repF.faults.any (·.startsWith "kernel:")
  check s!"forged proof: checkNode finds no fault, the kernel rejects ({repF.faults.size} fault), no record" okF

  -- 4. A missing reference with a statement to assume: `t3 := t2 1` packed
  -- without `t2`, whose statement unit is in the file (it is an entry).
  let (nodeU, _) ← packEnvironment env #[`t3, `f] true (cacheDir := none)
  let (_, repU) ← verifyNode base nodeU
  for f in repU.faults do IO.println s!"    fault: {f}"
  let t2stmt := (nodeU.entries.find? (·.name == `t2)).map (·.stmt)
  let okU := repU.faults.isEmpty && (match repU.records.find? (·.name == `t3), t2stmt with
    | some r, some s => r.valid && r.assumes == #[s] && repU.assumed.any (·.1 == `t2)
    | _, _ => false)
  check "t3 packed without t2: t2 assumed from its statement unit, t3's record assumes exactly it" okU

  -- 5. SHA-512 and Ed25519 (pure Lean) against FIPS 180-4 and RFC 8032.
  IO.println "Crypto:"
  let hex (b : ByteArray) := CA.SHA512.toHex b
  let unhex (s : String) : ByteArray := Id.run do
    let cs := s.toList.toArray
    let mut b := ByteArray.empty
    let v (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
    for i in [:cs.size / 2] do b := b.push (v cs[2*i]! * 16 + v cs[2*i+1]!).toUInt8
    return b
  check "sha512(\"\") is the FIPS vector"
    (hex (CA.SHA512.sha512 .empty) == "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e")
  check "sha512(\"abc\") is the FIPS vector"
    (hex (CA.SHA512.sha512 "abc".toUTF8) == "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")
  check "sha512 of 200 bytes (two blocks) agrees with hashlib"
    (hex (CA.SHA512.sha512 (ByteArray.mk ((Array.range 200).map (·.toUInt8)))) == "986058e9895e2c2ab8f9e8cbdf801db12a44842a56a91d5a4e87b1fc98b293722c4664142e42c3c551ff898646268cd92b84ed230b8c94bed7798d4f27cd7465")
  let seed := unhex "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
  let pk := unhex "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
  let sig := unhex "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
  check "ed25519: RFC 8032 test 1 public key" (CA.Ed25519.publicKey seed == pk)
  check "ed25519: RFC 8032 test 1 signature" (CA.Ed25519.sign seed .empty == sig)
  check "ed25519: RFC 8032 test 1 verifies" (CA.Ed25519.verify pk .empty sig)
  check "ed25519: a changed message fails" (!CA.Ed25519.verify pk "x".toUTF8 sig)
  let seed2 ← CA.Ed25519.randomSeed
  let pk2 := CA.Ed25519.publicKey seed2
  let msg := "the kernel accepted it".toUTF8
  let s2 := CA.Ed25519.sign seed2 msg
  check "ed25519: a fresh key signs and verifies; the other key does not" (CA.Ed25519.verify pk2 msg s2 && !CA.Ed25519.verify pk msg s2)
  let tampered := s2.set! 10 (s2[10]! ^^^ 1)
  check "ed25519: a flipped signature bit fails" (!CA.Ed25519.verify pk2 msg tampered)

  let fails ← failsRef.get
  IO.println (if fails == 0 then "verify-test: all passed" else s!"verify-test: {fails} FAILED")
  return if fails == 0 then 0 else 1

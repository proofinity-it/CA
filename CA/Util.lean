import Lean

open Lean

namespace CA

/-- Version of the byte-level encoding scheme behind every CA hash
    (`ExprHash.serializeExpr`, `RefHash`). Bumped whenever a change to the
    encoding changes ids for existing content; recorded in `meta.json` and
    mixed into the `RefHash` preimages so ids from different schemes can
    never coincide by accident.

    * 1 (all public releases, v0.1.0 on): Nat literals encoded as length-prefixed big-endian bytes
      (previously truncated to 64 bits, so `2^64` and `0` collided);
      universe levels normalised (`Level.normalize`) after positional
      renaming, so `max u v` and `max v u` agree. Scheme 0 (pre-release development only) carried
      no version byte. -/
def schemeVersion : Nat := 1

end CA

namespace CA.Util

/-- Minimal big-endian byte representation of a natural number
    (`0 ↦ #[]`, no leading zero bytes). Used, length-prefixed, to encode
    `Nat` literals in hash preimages without a 64-bit truncation. -/
def natToBytesBE (n : Nat) : ByteArray := Id.run do
  let mut acc : Array UInt8 := #[]
  let mut m := n
  while m > 0 do
    acc := acc.push (UInt8.ofNat (m % 256))
    m := m / 256
  return ByteArray.mk acc.reverse

/-- Collect the distinct named constants (`.const name _`) appearing in
    an expression, added to `acc`.

    Implemented with `Expr.foldConsts`, which visits each *shared*
    subterm once (pointer-cached), so the cost is the size of the DAG.
    The previous plain structural recursion re-walked every shared
    subterm and was exponential on the DAG-shaped proof terms `omega`,
    `decide` and `simp` produce — a single such term in `Init` or
    `Mathlib` could take minutes, which is what stalled a whole-Mathlib
    id computation before the first component was even hashed
    (2026-08-18). Same result set as before; only the walk changed. -/
def collectConstants (expr : Expr) (acc : Lean.NameSet := {}) : Lean.NameSet :=
  expr.foldConsts acc fun name (a : Lean.NameSet) => a.insert name

/-- Classify a `ConstantInfo` into its kind string. -/
def constantKind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo  _ => "axiom"
  | .defnInfo   _ => "definition"
  | .thmInfo    _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo   _ => "constructor"
  | .recInfo    _ => "recursor"

end CA.Util

/-!
# CA.Base58 — base58btc encoding for content-addressed hashes

Uses the Bitcoin alphabet (no `0`/`O`/`I`/`l`) for unambiguous, compact
hash rendering: a SHA-256 digest (32 bytes) encodes to 43–44 characters
vs 64 for hex.

Alphabet: `123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz`

This is the id rendering shared by everything downstream of CA
(declbuild's store keys, the same keys on every registry peer's Redis);
it lives here so that
consumers do not each carry their own copy.
-/

namespace CA.Base58

private def alphabet : Array Char :=
  "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz".toList.toArray

/-- Reverse lookup: character → index in the base58 alphabet. -/
private def charToIndex (c : Char) : Option Nat := Id.run do
  for i in [:alphabet.size] do
    if alphabet[i]! == c then return some i
  return none

/-- Convert a natural number to base58 digits (least significant first). -/
private def natToDigits (n : Nat) (acc : Array Char := #[]) : Array Char :=
  if h : n = 0 then acc
  else natToDigits (n / 58) (acc.push alphabet[n % 58]!)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)

/-- Convert a natural number to big-endian bytes. -/
private def natToBytes (n : Nat) (acc : List UInt8 := []) : List UInt8 :=
  if h : n = 0 then acc
  else natToBytes (n / 256) (UInt8.ofNat (n % 256) :: acc)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)

/-- Encode a `ByteArray` to a base58btc string. -/
def encode (bytes : ByteArray) : String :=
  if bytes.size == 0 then "" else Id.run do
  -- Count leading zero bytes → each maps to '1'
  let mut leadingZeros : Nat := 0
  for i in [:bytes.size] do
    if bytes.get! i == 0 then leadingZeros := leadingZeros + 1
    else break
  -- Convert to big-endian integer
  let mut n : Nat := 0
  for i in [:bytes.size] do
    n := n * 256 + (bytes.get! i).toNat
  -- Base58 digits (reversed) + leading '1's
  let digits := natToDigits n
  return String.ofList (List.replicate leadingZeros '1' ++ digits.reverse.toList)

/-- Decode a base58btc string to a `ByteArray`.
    Returns `none` on invalid characters. -/
def decode (s : String) : Option ByteArray :=
  if s.isEmpty then some ByteArray.empty else Id.run do
  let chars := s.toList
  -- Count leading '1's → each maps to 0x00
  let mut leadingOnes : Nat := 0
  for c in chars do
    if c == '1' then leadingOnes := leadingOnes + 1
    else break
  -- Convert remaining chars to big integer
  let remaining := chars.drop leadingOnes
  let mut n : Nat := 0
  for c in remaining do
    match charToIndex c with
    | some idx => n := n * 58 + idx
    | none => return none
  -- Convert to bytes and prepend leading zeros
  let dataBytes := if n == 0 then [] else natToBytes n
  let zeros : List UInt8 := List.replicate leadingOnes 0
  return some (ByteArray.mk (zeros ++ dataBytes).toArray)

/-- Heuristic: does `s` look like a base58btc-encoded SHA-256 (a CA
    hash) rather than a Lean declaration name?

    A 32-byte digest encodes to 43–44 base58 characters, so the test
    is "44 ± a couple of characters, all in the alphabet". Testing only
    "contains no `.`" is not enough: every top-level Lean name (`Nat`,
    `id`, `main_theorem`) also contains no dot and is made of base58
    letters. -/
def looksLikeCaHash (s : String) : Bool :=
  let n := s.length
  40 ≤ n && n ≤ 46 && s.all (fun c => (charToIndex c).isSome)

end CA.Base58

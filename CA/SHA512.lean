/-!
# CA.SHA512 — pure-Lean SHA-512 (FIPS 180-4)

Needed by Ed25519 (`CA.Ed25519`), which hashes with SHA-512. The round
constants and initial values are not typed in: they are computed from the
fractional parts of the cube and square roots of the first primes, as the
standard defines them, so a typo cannot slip in. The test executables
check the FIPS vectors for `""` and `"abc"`.
-/

namespace CA.SHA512

private def primes (n : Nat) : Array Nat := Id.run do
  let mut out := #[]
  let mut k := 2
  while out.size < n do
    if (List.range (k - 2)).all (fun d => d + 2 ≥ k || k % (d + 2) != 0) then out := out.push k
    k := k + 1
  return out

/-- Largest `r` with `r ^ e ≤ n`, by binary search. -/
private def iroot (n e : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := 1
  while hi ^ e ≤ n do hi := hi * 2
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if mid ^ e ≤ n then lo := mid else hi := mid
  return lo

private def mask64 : Nat := 2 ^ 64 - 1

/-- `K[t]` = first 64 bits of the fractional part of the cube root of the t-th prime. -/
def K : Array UInt64 :=
  (primes 80).map fun p => ((iroot (p * 2 ^ 192) 3) &&& mask64).toUInt64

/-- `H⁰` = first 64 bits of the fractional parts of the square roots of the first 8 primes. -/
def H0 : Array UInt64 :=
  (primes 8).map fun p => ((iroot (p * 2 ^ 128) 2) &&& mask64).toUInt64

@[inline] private def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))
@[inline] private def bigS0 (x : UInt64) : UInt64 := rotr x 28 ^^^ rotr x 34 ^^^ rotr x 39
@[inline] private def bigS1 (x : UInt64) : UInt64 := rotr x 14 ^^^ rotr x 18 ^^^ rotr x 41
@[inline] private def smallS0 (x : UInt64) : UInt64 := rotr x 1 ^^^ rotr x 8 ^^^ (x >>> 7)
@[inline] private def smallS1 (x : UInt64) : UInt64 := rotr x 19 ^^^ rotr x 61 ^^^ (x >>> 6)
@[inline] private def ch (e f g : UInt64) : UInt64 := (e &&& f) ^^^ ((~~~e) &&& g)
@[inline] private def maj (a b c : UInt64) : UInt64 := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

private def be64 (b : ByteArray) (i : Nat) : UInt64 := Id.run do
  let mut x : UInt64 := 0
  for k in [:8] do x := (x <<< 8) ||| b[i + k]!.toUInt64
  return x

private def pushBE64 (b : ByteArray) (x : UInt64) : ByteArray := Id.run do
  let mut b := b
  for k in [:8] do b := b.push ((x >>> (56 - 8 * k).toUInt64).toUInt8)
  return b

private def compress (h : Array UInt64) (block : ByteArray) (off : Nat) : Array UInt64 := Id.run do
  let k := K
  let mut w : Array UInt64 := Array.mkEmpty 80
  for t in [:16] do w := w.push (be64 block (off + 8 * t))
  for t in [16:80] do
    w := w.push (smallS1 w[t-2]! + w[t-7]! + smallS0 w[t-15]! + w[t-16]!)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for t in [:80] do
    let t1 := hh + bigS1 e + ch e f g + k[t]! + w[t]!
    let t2 := bigS0 a + maj a b c
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- SHA-512 of `msg`, 64 bytes. -/
def sha512 (msg : ByteArray) : ByteArray := Id.run do
  let n := msg.size
  let mut m := msg.push 0x80
  while m.size % 128 != 112 do m := m.push 0
  m := pushBE64 m 0                      -- high 64 bits of the 128-bit bit length
  m := pushBE64 m (8 * n).toUInt64
  let mut h := H0
  let mut off := 0
  while off < m.size do
    h := compress h m off
    off := off + 128
  let mut out := ByteArray.empty
  for x in h do out := pushBE64 out x
  return out

def toHex (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let hex := "0123456789abcdef".toList
    String.ofList [hex[(x.toNat / 16)]!, hex[(x.toNat % 16)]!])

end CA.SHA512

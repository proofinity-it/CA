/-!
# CA.SHA256 — SHA-256 for content addressing

The library is pure Lean: `sha256Pure` is a FIPS 180-4 implementation
with no native dependency, so `require ca` needs no C toolchain, system
headers or link flags, and it runs unchanged in interpreted contexts
(the `#ca_registry` command during elaboration).

Bulk hashing can be faster. Every hashing entry point
(`RefHash.computeIds`, `ExprHash.compute*Hashes`) takes a `Hasher`,
defaulting to `pureHasher`; the `ca` CLI package (`cli/`) plugs in an
OpenSSL-backed one (`CA.SHA256.FFI.sha256`, ~2.5× faster end to end on
`Init`) and `ca selftest` cross-checks the two on test vectors. Whatever
the hasher, the digests — and therefore the ids — are identical.
-/

namespace CA.SHA256

/-- A SHA-256 implementation: 32-byte digest of a byte array, in `IO` so
    that FFI-backed implementations fit. -/
abbrev Hasher := ByteArray → IO ByteArray

/-! ## Pure-Lean SHA-256 (FIPS 180-4) -/

namespace Pure

private def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

@[inline] private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

end Pure

/-- Pure-Lean SHA-256 of a `ByteArray` (32-byte digest). The library's
    default hasher; usable from interpreted code where extern symbols are
    not loaded (e.g. commands and attributes running during elaboration). -/
def sha256Pure (data : ByteArray) : ByteArray := Id.run do
  -- Padding: 0x80, zeros to 56 mod 64, then the bit length, big-endian.
  let len := data.size
  let mut msg := data.push 0x80
  while msg.size % 64 != 56 do
    msg := msg.push 0
  let bitLen : UInt64 := (len * 8).toUInt64
  for i in [:8] do
    msg := msg.push (bitLen >>> ((7 - i.toUInt64) * 8)).toUInt8
  -- Compression.
  let mut h0 : UInt32 := 0x6a09e667
  let mut h1 : UInt32 := 0xbb67ae85
  let mut h2 : UInt32 := 0x3c6ef372
  let mut h3 : UInt32 := 0xa54ff53a
  let mut h4 : UInt32 := 0x510e527f
  let mut h5 : UInt32 := 0x9b05688c
  let mut h6 : UInt32 := 0x1f83d9ab
  let mut h7 : UInt32 := 0x5be0cd19
  let nBlocks := msg.size / 64
  for blk in [:nBlocks] do
    let base := blk * 64
    let mut w : Array UInt32 := Array.mkEmpty 64
    for t in [:16] do
      let o := base + t * 4
      w := w.push <|
        (msg.get! o).toUInt32 <<< 24 ||| (msg.get! (o+1)).toUInt32 <<< 16 |||
        (msg.get! (o+2)).toUInt32 <<< 8 ||| (msg.get! (o+3)).toUInt32
    for t in [16:64] do
      let s0 := Pure.rotr w[t-15]! 7 ^^^ Pure.rotr w[t-15]! 18 ^^^ (w[t-15]! >>> 3)
      let s1 := Pure.rotr w[t-2]! 17 ^^^ Pure.rotr w[t-2]! 19 ^^^ (w[t-2]! >>> 10)
      w := w.push (w[t-16]! + s0 + w[t-7]! + s1)
    let mut a := h0
    let mut b := h1
    let mut c := h2
    let mut d := h3
    let mut e := h4
    let mut f := h5
    let mut g := h6
    let mut h := h7
    for t in [:64] do
      let S1 := Pure.rotr e 6 ^^^ Pure.rotr e 11 ^^^ Pure.rotr e 25
      let ch := (e &&& f) ^^^ (~~~e &&& g)
      let t1 := h + S1 + ch + Pure.k[t]! + w[t]!
      let S0 := Pure.rotr a 2 ^^^ Pure.rotr a 13 ^^^ Pure.rotr a 22
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let t2 := S0 + maj
      h := g; g := f; f := e; e := d + t1
      d := c; c := b; b := a; a := t1 + t2
    h0 := h0 + a; h1 := h1 + b; h2 := h2 + c; h3 := h3 + d
    h4 := h4 + e; h5 := h5 + f; h6 := h6 + g; h7 := h7 + h
  let mut out := ByteArray.emptyWithCapacity 32
  for hw in [h0, h1, h2, h3, h4, h5, h6, h7] do
    out := out.push (hw >>> 24).toUInt8
    out := out.push (hw >>> 16).toUInt8
    out := out.push (hw >>> 8).toUInt8
    out := out.push hw.toUInt8
  return out

/-- The library default `Hasher`: `sha256Pure` in `IO`. -/
def pureHasher : Hasher := fun data => pure (sha256Pure data)

/-- SHA-256 in `IO`. Kept under the name of the former OpenSSL FFI binding
    for API compatibility; it is `sha256Pure` (same digests).
    For an FFI-backed hasher see `CA.SHA256.FFI` in the `cli/` package. -/
def sha256 (data : ByteArray) : IO ByteArray := pure (sha256Pure data)

private def hexDigit (n : UInt8) : Char :=
  let n := n.toNat
  if n < 10 then Char.ofNat (n + 48)
  else Char.ofNat (n - 10 + 97)

/-- Convert a 32-byte ByteArray to a 64-character hex string. -/
def toHex256 (bytes : ByteArray) : String := Id.run do
  let mut chars : Array Char := Array.mkEmpty (bytes.size * 2)
  for i in [:bytes.size] do
    let b := bytes.get! i
    chars := chars.push (hexDigit (b >>> 4))
    chars := chars.push (hexDigit (b &&& 0x0F))
  return String.ofList chars.toList

end CA.SHA256

import CA.SHA512

/-!
# CA.Ed25519 — pure-Lean Ed25519 (RFC 8032)

Signatures on verification records, bindings and namespace claims
(`registry-protocol.md` §3, §7). Pure Lean over `Nat`, so the library
keeps no native dependency and a signature can be checked inside a
`lake build`; `tools/ed25519_ref.py` is the same algorithm in Python's
standard library, for `tools/registry_ref.py`. Not constant-time: fine
for verification, and signing happens on the signer's machine with the
signer's key.

Keys: a 32-byte seed is the secret key; the public key is 32 bytes. A
signature is 64 bytes. `CA.Ed25519.keyText` renders a public key as
base58 for namespace ids (`label@key`).
-/

namespace CA.Ed25519

/-- The field prime 2^255 − 19. -/
def p : Nat := 2 ^ 255 - 19
/-- The group order of the base point. -/
def L : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

private def powMod (b e m : Nat) : Nat := Id.run do
  let mut r := 1
  let mut b := b % m
  let mut e := e
  while e > 0 do
    if e % 2 == 1 then r := r * b % m
    b := b * b % m
    e := e / 2
  return r

private def inv (x : Nat) : Nat := powMod x (p - 2) p
private def sub (a b : Nat) : Nat := (a + p - b % p) % p

/-- d = −121665 / 121666 mod p. -/
def d : Nat := sub 0 (121665 * inv 121666 % p)

/-- A point in extended coordinates (X, Y, Z, T), x = X/Z, y = Y/Z, xy = T/Z. -/
structure Point where
  x : Nat
  y : Nat
  z : Nat
  t : Nat

def Point.zero : Point := ⟨0, 1, 1, 0⟩

/-- Unified addition (RFC 8032 §5.1.4). -/
def Point.add (P Q : Point) : Point :=
  let a := sub P.y P.x * sub Q.y Q.x % p
  let b := (P.y + P.x) * (Q.y + Q.x) % p
  let c := P.t * 2 % p * d % p * Q.t % p
  let dd := P.z * 2 % p * Q.z % p
  let e := sub b a
  let f := sub dd c
  let g := (dd + c) % p
  let h := (b + a) % p
  ⟨e * f % p, g * h % p, f * g % p, e * h % p⟩

def Point.double (P : Point) : Point :=
  let a := P.x * P.x % p
  let b := P.y * P.y % p
  let c := 2 * (P.z * P.z % p) % p
  let h := (a + b) % p
  let s := (P.x + P.y) % p
  let e := sub h (s * s % p)
  let g := sub a b
  let f := (c + g) % p
  ⟨e * f % p, g * h % p, f * g % p, e * h % p⟩

/-- `n · P`, double-and-add from the top bit. -/
def Point.mul (P : Point) (n : Nat) : Point := Id.run do
  let mut r := Point.zero
  let mut q := P
  let mut n := n
  while n > 0 do
    if n % 2 == 1 then r := r.add q
    q := q.double
    n := n / 2
  return r

/-- The base point: y = 4/5, x the positive root. -/
def B : Point :=
  let y := 4 * inv 5 % p
  let x := 15112221349535400772501151409588531511454012693041857206046113283949847762202
  ⟨x, y, 1, x * y % p⟩

private def toLE (n : Nat) (len : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  let mut n := n
  for _ in [:len] do
    b := b.push (n % 256).toUInt8
    n := n / 256
  return b

private def ofLE (b : ByteArray) : Nat :=
  b.data.foldr (fun x acc => acc * 256 + x.toNat) 0

/-- Encode a point: y in 255 bits little-endian, the sign of x in the top bit. -/
def Point.encode (P : Point) : ByteArray :=
  let zi := inv P.z
  let x := P.x * zi % p
  let y := P.y * zi % p
  toLE (y + (if x % 2 == 1 then 2 ^ 255 else 0)) 32

/-- Decode a point; `none` if the bytes are not on the curve. -/
def Point.decode (b : ByteArray) : Option Point := do
  if b.size != 32 then none
  let n := ofLE b
  let sign := n / 2 ^ 255
  let y := n % 2 ^ 255
  if y ≥ p then none
  let y2 := y * y % p
  let u := sub y2 1
  let v := (d * y2 + 1) % p
  -- x² = u/v; x = (u/v)^((p+3)/8), fixed up by √−1 when needed.
  let mut x := powMod (u * inv v % p) ((p + 3) / 8) p
  if (x * x % p) != u * inv v % p then
    x := x * powMod 2 ((p - 1) / 4) p % p
  if (x * x % p) != u * inv v % p then none
  if x == 0 && sign == 1 then none
  if x % 2 != sign then x := sub 0 x
  return ⟨x, y, 1, x * y % p⟩

private def clamp (h : ByteArray) : Nat :=
  let h := h.set! 0 (h[0]! &&& 248)
  let h := h.set! 31 ((h[31]! &&& 63) ||| 64)
  ofLE (h.extract 0 32)

/-- The public key of a 32-byte seed. -/
def publicKey (seed : ByteArray) : ByteArray :=
  let h := CA.SHA512.sha512 seed
  (B.mul (clamp h)).encode

/-- Sign `msg` with a 32-byte seed; 64 bytes. -/
def sign (seed msg : ByteArray) : ByteArray :=
  let h := CA.SHA512.sha512 seed
  let s := clamp h
  let pre := h.extract 32 64
  let pk := (B.mul s).encode
  let r := ofLE (CA.SHA512.sha512 (pre ++ msg)) % L
  let rEnc := (B.mul r).encode
  let k := ofLE (CA.SHA512.sha512 (rEnc ++ pk ++ msg)) % L
  rEnc ++ toLE ((r + k * s) % L) 32

/-- Check a 64-byte signature of `msg` under a 32-byte public key. -/
def verify (pk msg sig : ByteArray) : Bool := Id.run do
  if sig.size != 64 || pk.size != 32 then return false
  let some R := Point.decode (sig.extract 0 32) | return false
  let some A := Point.decode pk | return false
  let s := ofLE (sig.extract 32 64)
  if s ≥ L then return false
  let k := ofLE (CA.SHA512.sha512 (sig.extract 0 32 ++ pk ++ msg)) % L
  (B.mul s).encode == (R.add (A.mul k)).encode

/-- A fresh random seed (secret key). -/
def randomSeed : IO ByteArray := IO.getRandomBytes 32

end CA.Ed25519

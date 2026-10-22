import CA.SHA256

/-!
# CA.SHA256.FFI — OpenSSL-backed SHA-256 for the `ca` CLI

The library (`CA.SHA256`) is pure Lean. This module, which lives in the
`cli/` package together with its C shim (`c/sha256_shim.c`, OpenSSL EVP),
provides a faster `Hasher` for bulk indexing. `ca selftest` checks that
it agrees with `sha256Pure` on test vectors; ids never depend on which
one computed them.
-/

namespace CA.SHA256.FFI

/-- SHA-256 via OpenSSL EVP (`lean_sha256_hash` in `c/sha256_shim.c`). -/
@[extern "lean_sha256_hash"]
opaque sha256 (data : @& ByteArray) : IO ByteArray

/-- `sha256` as a `CA.SHA256.Hasher`. -/
def hasher : Hasher := fun data => sha256 data

end CA.SHA256.FFI

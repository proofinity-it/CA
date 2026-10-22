import Lake
open System Lake DSL

/-! `ca` command-line tool: batch indexing into Redis (`fetch`, `address`),
JSON manifests, registry generation (`registry`), node files (`pack`,
`check`; SQLite through leansqlite), and `selftest`.

A separate package from the library in `..` so that `require ca` stays
pure Lean. This package owns every native dependency: OpenSSL (the
SHA-256 accelerator in `c/sha256_shim.c`) and, through redis-lean,
hiredis and zlog. Build with `lake build` in this directory. The link
flags below are the Ubuntu/Debian locations; inside `nix develop` the
same libraries are found through `LIBRARY_PATH` and the stray `-L`s are
harmless. -/

package «ca-cli» where
  extraDepTargets := #[`libsha256_shim]

require ca from ".."

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "v4.35.0"

require redisLean from git
  "https://github.com/proofinity-it/redis-lean" @ "v4.35.0-3"

/-- SQLite for the node file (`ca pack` / `ca check`). Bundles the SQLite
    amalgamation: no system library. -/
require leansqlite from git
  "https://github.com/leanprover/leansqlite" @ "v4.35.0"

/-- OpenSSL-backed `CA.SHA256.FFI.sha256`. -/
lean_lib CaCli

-- The target is `caExe` because `ca` is already the name of the library
-- dependency above; the binary is still `.lake/build/bin/ca`.
@[default_target]
lean_exe caExe where
  exeName := "ca"
  root := `Main
  supportInterpreter := true
  -- supportInterpreter makes undefined symbols fatal at link time, so the
  -- native deps of the transitive redis-lean/zlog-lean shims must be
  -- resolved here explicitly.
  moreLinkArgs := #[
    "-L/usr/lib/x86_64-linux-gnu", "-lhiredis", "-lhiredis_ssl",
    "-L/usr/local/lib", "-Wl,-rpath,/usr/local/lib", "-lzlog",
    "-lssl", "-lcrypto"]

/-- Compile `src` into `oFile` with a build trace over `src` and `deps` (local headers,
    `#include`d `.c` files), so editing any of them rebuilds the object and the archives
    that use it. `weakArgs` (include paths) are kept out of the trace. -/
def tracedO (oFile src : FilePath) (deps : Array FilePath := #[])
    (weakArgs traceArgs : Array String := #[]) : SpawnM (Job FilePath) := do
  let inputs ← (#[src] ++ deps).mapM inputTextFile
  let srcJob ← (Job.collectArray inputs).mapM fun _ => pure src
  buildO oFile srcJob weakArgs traceArgs

target sha256_shim_o pkg : FilePath := do
  tracedO (pkg.buildDir / "c" / "sha256_shim.o") (pkg.dir / "c" / "sha256_shim.c")
    (weakArgs := #["-I", (← getLeanIncludeDir).toString])
    (traceArgs := #["-fPIC", "-O2"])

extern_lib libsha256_shim pkg := do
  let obj ← sha256_shim_o.fetch
  let name := nameToStaticLib "sha256_shim"
  buildStaticLib (pkg.staticLibDir / name) #[obj]

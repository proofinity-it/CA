# Building and dependencies

The repository holds two Lake packages:

| Directory | Package | Contents | Native deps |
|---|---|---|---|
| `.` | `ca` | the `CA` library (default target, precompiled) and the test executables `refhash-test`, `registry-test`, `payload-test` | **none**: pure Lean, Batteries only |
| `cli/` | `ca-cli` | the `ca` command-line tool; `cli/tests/node-test.sh` (pack / check end to end on a fixture project) | OpenSSL, hiredis (+ zlog via redis-lean); SQLite is bundled by leansqlite |

The library is what downstream projects `require`; it hashes with a
pure-Lean SHA-256 and needs no system headers or link flags on any
platform. It is built with `precompileModules`, so a downstream
`lake build` also compiles CA (and the Batteries modules it imports) to
shared libraries with the toolchain's bundled compiler — a one-time cost
that lets `#ca_registry` run compiled code during elaboration. The CLI owns every native dependency and plugs an
OpenSSL hasher into the same APIs (`ca selftest` cross-checks the two;
ids are identical either way).

```bash
# Library and tests (any platform, nothing to install)
lake build
lake exe refhash-test
lake exe registry-test
lake exe payload-test     # ~5 min: round-trips every Init declaration

# CLI (Linux; needs the OpenSSL and hiredis development packages)
cd cli
lake build
.lake/build/bin/ca --help
tests/node-test.sh        # ca pack / ca check end to end on tests/fixture
```

## With Nix

```bash
nix develop            # dev shell (or use direnv with the included .envrc)
lake build             # library
(cd cli && lake build) # CLI: the shell provides openssl, hiredis, zlog
```

The Nix flake provides the Lean 4 release binary pinned to the same
version as `lean-toolchain` (v4.35.0; x86_64 and aarch64, Linux and
macOS) and the CLI's native libraries. When bumping the toolchain, bump
`leanVersion` and the four tarball hashes in `flake.nix` together (the
recipe is in the file), and `cli/lean-toolchain` alongside
`lean-toolchain`.

## Without Nix (Ubuntu/Debian)

```bash
lake build                                   # library: nothing to install
sudo apt install libssl-dev libhiredis-dev   # CLI only
cd cli && lake build
```

The CLI's link flags name the Ubuntu library locations
(`cli/lakefile.lean`); adjust them for other distributions.

# Dependencies

| Dependency | Required by | Purpose |
|---|---|---|
| [batteries](https://github.com/leanprover-community/batteries) | library | `NameMapExtension` for registry attributes |
| [lean4-cli](https://github.com/leanprover/lean4-cli) | `cli/` | argument parsing |
| [redis-lean](https://github.com/proofinity-it/redis-lean) | `cli/` | Redis (hiredis) for `fetch`/`address` |
| [leansqlite](https://github.com/leanprover/leansqlite) | `cli/` | SQLite for node files (`pack` / `check`); bundles the SQLite amalgamation, so no system library; needs a C compiler `cc` |
| OpenSSL (`libssl`, `libcrypto`) | `cli/` | SHA-256 accelerator (`CA.SHA256.FFI`) |

A project that `require`s `ca` fetches Batteries and nothing else: Lake
resolves a package's dependencies from its own lakefile, and the
library's lakefile requires only Batteries. The CLI's dependencies live
in `cli/lakefile.lean` and are never seen by downstream projects.

Lean toolchain: `leanprover/lean4:v4.35.0` (see `lean-toolchain`;
`batteries` / `Cli` are pinned to the matching releases). This
repository's own tags are release versions, starting at `v0.1.0`;
see [CHANGELOG.md](../CHANGELOG.md). Every hash is computed under an
encoding-scheme version (`CA.schemeVersion`, recorded in `meta.json` and
mixed into every `RefHash` preimage); a bump means ids changed.

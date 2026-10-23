# Modules

## Core — content addressing engine

| Module | Description |
|--------|-------------|
| `CA.Canonical` | L0 (pure) and L1 (MetaM) canonicalization; positional universe renaming for declarations, level normalisation |
| `CA.SHA256` | Pure-Lean SHA-256 (`sha256Pure`, FIPS 180-4) and the `Hasher` hook through which the CLI plugs in OpenSSL (`CA.SHA256.FFI`, in `cli/`) |
| `CA.Base58` | base58btc encode/decode for id rendering |
| `CA.ExprHash` | Expr serialization, `DeclHash`, name-based batch hashing (the registry's `type_hash`) |
| `CA.RefHash` | `stmt` / `decl` / `ref` ids: name-free content identity per declaration (proof-irrelevant references for theorems, value-inclusive otherwise), Merkle-hashed expressions, SCC blocks for mutual/inductive families; `stmtIdOf` for bare statements; `withProofs := false` for statement cones — see [`docs/ref-hash.md`](ref-hash.md); tests: `lake exe refhash-test` |
| `CA.Payload` | the stored form of a declaration ([`docs/payload.md`](payload.md)): `encodeUnit` / `encodeStatement` (declarations → unit with name slots + decorations, self-checked by rebuilding), `checkUnit` (ids recomputed from a unit's bytes and the file's ref table), `decodeUnit` / `decodeDecoration` / `rebuild`; tests: `lake exe payload-test` |
| `CA.Node` | the rows of a registry node (`registry-protocol.md` §12): `packDecls` (declarations + the ids of what they reference → units, members, decorations, declaration / witness rows; no `Environment`, so a store can pack from what it holds; a block with a member missing is refused), `packEnvironment` (the cone walked in an environment, then `packDecls`, plus statement units and entries), `checkNode` (every row against its unit, every decoration rebuilt); no file format — `CA.NodeFile` (package `nodefile/`, module `CaNodeFile`) writes and reads them as SQLite, for `ca pack` / `ca check` and for other stores; tests: `lake exe node-test` |
| `CA.Sources` | `sources.json` (folder and node sources, paths or URLs), reading a registry folder, lookups by `stmt` / `type_hash` / name over folder sources; node sources are the CLI's (`ca lookup`) |
| `CA.Resolve` | `#ca_lookup` (the folder sources' answer, as a message) and `resolve% "<stmt>"` (the proof a source binds to a statement, if in scope and recomputing to that `stmt`); tests: `lake exe registry-test` |
| `CA.Export` | JSON manifest, TSV edge list, summary statistics |
| `CA.Util` | `collectConstants`, `constantKind`, `natToBytesBE`; `CA.schemeVersion` |

## Registry — decentralized publication

| Module | Status | Description |
|--------|--------|-------------|
| `CA.Registry.Basic` | implemented | `OpenPointEntry`, `PublishEntry` structures, `NameMapExtension`s, query API |
| `CA.Registry.Attributes` | implemented | `@[publish]` and `@[open_point]` attribute registration and validation |
| `CA.Registry.Generate` | implemented | `#ca_registry` command: exact ids over the statement cone with a cached base table (`computeEntryIds`), status classification (`classify`), JSON output written only on change; tests: `lake exe registry-test` |
| `CA.Resolve` | partly | `#ca_lookup`, `resolve%` implemented (see above); `use` / `use!` (a declaration not in scope, rebuilt from a node file) not yet |
| `CA.Registry.Sources` | not yet | `sources.json` parsing, remote registry fetching, local cache |

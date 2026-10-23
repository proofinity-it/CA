# Development plan

Status: **working plan** (2026-10-23). What is left to build in CA once the
identity scheme ([spec.md](spec.md)) and the payload format
([payload.md](payload.md)) are fixed. Each item names what it unlocks,
what it delivers and how it is known to be done. Items are in the order
they are meant to be built; later items use the earlier ones. The
protocol's own sequencing is [registry-protocol.md](registry-protocol.md)
§17; this plan is the engineering behind it. Each item carries a status
line kept current as work lands.

The constraint every item respects: the `ca` library stays pure Lean.
Anything that needs SQLite lives in `nodefile/`; anything that needs
OpenSSL, Redis, HTTP or a signing library lives in `cli/`. So a feature
has two faces when both are wanted: a pure one over the registry folder
(JSON), usable from inside a `lake build`, and a full one over node
files, in the CLI.

## 1. A node you can consume

Today a registry is publishable as a folder or a node file and a file is
checkable, but nothing reads one back into a build. This is the gap the
README states.

| deliverable | where | done when |
|---|---|---|
| `sources.json`: a list of sources, each a registry folder or a node file, local path or URL, with an optional expected key | `CA.Sources` (pure: parse, resolve local paths, cache dir) | parsed and validated; a project-local file and `--sources` both work |
| Fetching a remote source into `.lake/ca/sources/` | CLI (`curl` subprocess; the library reads only local copies) | a URL source is fetched once and reused while its digest matches |
| `ca lookup`: by `stmt`, by `type_hash`, or by name; answers status, project, witnesses, declarations, across every source in order | CLI over node files (SQL queries in `CA.NodeFile`) and folders | the question "has this been proved, by whom, under which assumptions" is answered from local sources |
| `#ca_lookup` inside Lean: the same question against folder sources, without leaving the editor | `CA.Sources` + a command elaborator | the fixture's registry answers for its own entries |
| `resolve% "<stmt>"`: a term whose value is the constant that a source binds to that statement, when the constant is in the environment; a clear error naming the project otherwise | term elaborator in the library | `resolve%` of `conj_literal`'s `stmt` elaborates to `conj_literal` |

Bringing a declaration that is *not* in the environment into scope
(rebuilding it from a node file's unit) is item 2's `ca verify`
machinery turned around; it is deliberately not in this item.

Status: **not started.**

## 2. CA alone as a checker node

`ca check` proves a file's ids are honest. Only the kernel proves the
mathematics is. With this item a node file carries kernel-checked
records, which is what the protocol's "proved" derives from.

| deliverable | where | done when |
|---|---|---|
| `deps` rows: for each packed declaration, the `ref` ids it cites, derived from its unit | `CA.Node` (pack and check), `CA.NodeFile` | `ca check` confirms every `deps` row against the unit's reference slots |
| `ca verify FILE`: rebuild every declaration from its unit and decorations, add it to an environment on the file's toolchain foundations first, and let the kernel judge; open statements and missing references become axioms of their type and are listed as `assumes` | CLI (`CA.Verify` in the library for the pure part) | the fixture packs with `--own`, verifies clean, and a tampered proof term is rejected by the kernel |
| `records` rows: one per verified witness, `assumes` as ref ids, `axioms` from `collectAxioms`, toolchain, policy; a record with `sorryAx` is written as invalid | `CA.Node`, `CA.NodeFile`, `tools/registry_ref.py` reads them | `ca verify` writes them; the Python checker lists them and derives "proved" over them |
| Signatures: Ed25519 over the record digest, signer key in `meta` | CLI, through libsodium-lean | a record signed by one key is rejected under another |
| `bindings` rows: signed, sequence-numbered `(ns, name) → ref` | same | last-writer-wins is gone from the file format |

Status: **not started.**

## 3. Merge and reconciliation between static nodes

The protocol says "merge is SQL". Nothing does it yet.

| deliverable | where | done when |
|---|---|---|
| `remap`: re-encode a unit and its decorations against another file's ref and name tables, ids unchanged, variant digest recomputed | `CA.Payload` | every Init unit remapped onto a shuffled table checks to the same key |
| `ca merge OUT A B…`: union of nodes; faults reported, naming variants kept, witnesses and records unioned, entries keyed by `(name, stmt)` | `CA.Node.merge`, CLI | merging a node with itself is the identity up to row order; merging the fixture's three packs checks clean |
| `ca digest FILE`: range digests over sorted keys (prefix buckets); `ca diff A B`: the keys that differ, found by recursing only into differing buckets | `CA.Node`, CLI | two nodes differing in one unit exchange a handful of bucket digests and name that unit |

Status: **not started.**

## 4. Trusting the implementation

| deliverable | where | done when |
|---|---|---|
| Continuous integration: library build, the four test executables, `ca selftest`, both Python checkers, the CLI build and `node-test.sh`, on Ubuntu with elan, on every push and pull request | `.github/workflows/ci.yml` | green on `main` |
| Decoration test vectors: fixed bytes for the four §9 units' decorations | `payload.md` §9, `registry_ref.py --vectors`, `payload-test` | both checkers reproduce them |
| Fuzzing the checkers: random byte, row and table mutations of a node file; `ca check` and `registry_ref.py` must report a fault and never crash | `tools/fuzz_node.py` | 1,000 mutations of the fixture node, no crash, every mutation that changes a checked column is reported |
| Property tests for the payload codec: random well-formed units round-trip through encode, decode and check | `PayloadTest.lean` | 1,000 random units pass |
| Measurement A: full-mode versus statement-mode `stmt` agreement on Init | `tools/measure.sh`, results in `payload.md` or `ref-hash.md` | a number, with the method |
| Measurement B: `stmt` and `type_hash` survival across one toolchain bump on Init (v4.34.0 → v4.35.0) | same | a number, with the method; the "core cut" variant waits for the middle-tier scheme decision ([registry-protocol.md](registry-protocol.md) §16) |

Status: **not started.**

## 5. Scale

Init packs in about 2.5 minutes; Mathlib is about forty times larger.

| deliverable | where | done when |
|---|---|---|
| Profile `ca pack` and remove the obvious costs | `CA.Node`, `CA.Payload` | Init packs in under a minute on the same machine |
| Parallel encoding: blocks encoded against local tables in tasks, remapped onto the file table (item 3's `remap`) | `CA.Node.packDecls` | rows identical to the sequential pack, byte for byte |
| Incremental pack: `--base PREVIOUS.sqlite` reuses the units of declarations whose `decl` is unchanged | `CA.Node`, CLI | repacking an unchanged project re-encodes nothing |
| Compression: zstd for units, with and without a trained dictionary, measured | `nodefile/` (zstd would be a native dependency; measure first) | a size table in `payload.md` §7, then a decision |

Status: **not started.**

## 6. Toolchain releases

| deliverable | where | done when |
|---|---|---|
| `ca migrate A B`: pair the entries of two nodes on different toolchains by `type_hash`, confirm by `stmt`, and report what survived, what moved and what broke | `CA.Node`, CLI | measurement B is its output on Init |

Status: **not started.**

## 7. Smaller things

| deliverable | done when |
|---|---|
| An example project a reader can look at without building: the fixture's `registry/` folder and a node file committed, with a README | the files are in the repository and CI checks they are current |
| `payload.md` §8: drop "naming variants in the protocol", which §6 of the protocol settled | done in the same change as this plan |
| `docs/building.md` and the README building row say three packages | done in the same change as this plan |

Status: **not started.**

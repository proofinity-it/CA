# Changelog

## Unreleased

- `docs/payload.md`, draft 1: the stored form of a declaration in a
  node file. A per-file ref table; units (standalone, block or
  statement) with the canonical terms as one shared node table, from
  which the ids are recomputed without Lean or the cone; decorations
  keyed by (`decl`, name) for everything the ids ignore. Sized on 4,827
  Mathlib declarations with declbuild's `payload-probe`: 131% of
  declbuild's payload with per-file tables, 230% with ids inline.
  `registry-protocol.md` §4 and §12 use it; `spec.md` points to it.

- CA is the specification of the registry, implementations hold nodes:
  `docs/registry-protocol.md` §1 adds static nodes (the SQLite file,
  CA alone, nothing to host) and live nodes (a working store that
  exports and imports the file; declbuild's is Redis), independent of
  checker / mirror; §12 makes the SQLite file normative for
  interchange and calls Redis one live store, not part of the protocol.
  README and `docs/cli.md` say the same (the CLI's `ca:decl:*` keys are
  a local index, not a node).

- `docs/registry-protocol.md` draft 2: SQLite file as the published node
  format; checkers and mirrors; base-axiom policy; relative verification
  first; the exact tier's practical reach and the middle-tier question;
  reference implementation and sequencing.
- README: the "How it works" and "What it is for" sections moved to
  `docs/how-it-works.md` and `docs/what-it-is-for.md`; "The identity"
  folded into `docs/ref-hash.md`. All three listed in the documentation
  table. The prototype warning under the banner replaced by a status
  line next to the quick start.
- README: a short "The registry" section before the objects table,
  pointing at the two specification documents.
- README: the objects table rewritten with four columns (object, how you
  find it, unchanged by, changed by); `ref` explained as the embedding
  rule rather than a row; weaknesses named explicitly.
- `cli/lake-manifest.json` pins the rewritten redis-lean, arrow-lean and
  zlog-lean histories (same tags, new hashes).

## v0.1.0 — 2026-10-22 — first public release

Content-addressed identity for Lean 4 declarations, encoding scheme 1.

- **Ids.** `CA.RefHash` computes `stmt` / `decl` / `ref` per declaration:
  references embedded by their own ids, SCC blocks for mutual and
  inductive families, proof-irrelevant references for theorems.
  Full-precision `Nat` literals, normalised universe levels, a scheme
  version byte in every preimage. Normative byte-level specification in
  `docs/spec.md`, with an independent Python implementation
  (`tools/refhash_ref.py`) that reproduces its test vectors.
- **Registry.** `@[publish]` / `@[open_point]` attributes and
  `#ca_registry`: one entry per annotated declaration with a two-tier key
  (exact `stmt` / `ref`, coarse name-based `type_hash`), statuses
  `open` / `proved` / `conditional` / `definition` / `axiom` with
  `proves` / `proved_by` / `status_deps` and the within-registry cascade.
  Exact ids are computed over the statement cone, with the imported part
  cached under `.lake/ca/`; CA's modules are precompiled so this runs at
  elaboration time. Files are rewritten only when their content changes.
- **Packaging.** The `CA` library is pure Lean and requires only
  Batteries. The `ca` CLI (Redis indexing, manifests, `registry`,
  `selftest`, OpenSSL-backed hashing) is a separate package in `cli/`.
- **Tests.** `lake exe refhash-test` (properties and golden ids) and
  `lake exe registry-test` (status rules, exact ids, cache).
- **Docs.** README, usage, CLI, building, modules, scope and related
  work, worked example, RefHash, specification, registry design and a
  draft registry protocol, indexed in `docs/README.md`.

Development before this release, including encoding scheme 0 (no
version byte, 64-bit-truncated literals, syntactic universe levels), is
not part of the public history. Ids from scheme 0 are not comparable
with scheme 1.

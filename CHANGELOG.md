# Changelog

## Unreleased

- `docs/registry-protocol.md` draft 2: SQLite file as the published node
  format; checkers and mirrors; base-axiom policy; relative verification
  first; the exact tier's practical reach and the middle-tier question;
  reference implementation and sequencing.
- README: the "How it works" and "What it is for" sections moved to
  `docs/how-it-works.md` and `docs/what-it-is-for.md`, listed in the
  documentation table.
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

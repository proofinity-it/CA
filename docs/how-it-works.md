# How it works

The two mechanisms CA implements today: how an address is computed from
a declaration, and how a project publishes the addresses of the
declarations it chooses to. The identity scheme itself is in
[ref-hash.md](ref-hash.md) and, byte by byte, in [spec.md](spec.md);
the registry format is in [registry-design.md](registry-design.md).

## Content addressing

1. **Canonicalize** the type expression (strip metadata, rename universe
   params to positional indices, normalise universe levels, optionally
   unfold reducibles via `whnf`)
2. **Serialize** the canonical `Expr` to a tagged byte format
3. **Hash** with SHA-256 (pure Lean; the CLI plugs in OpenSSL for speed)

Two canonicalization levels:

| Level | What it does | Requires |
|-------|-------------|----------|
| L0 (default) | Universe renaming, level normalisation, mdata stripping | Pure |
| L1 | L0 + reducible-transparency `whnf` normalization | MetaM |

`CA.ExprHash` also keeps the older **name-based** hash, in which a
`.const` reference is the declaration's `Name` string: fast and stable
across toolchains, but blind — two libraries whose `IsSolvable` differ
hash a theorem about it identically. `CA.RefHash` supersedes it for
identity purposes; the name-based hash is worth keeping as a coarse,
version-spanning handle, and the registry emits both (see below). An
intermediate "content-based" mode, which embedded the referenced
declaration's *type* hash, was removed before v0.1.0.

See [address.md](address.md) for the full addressing design.

## Decentralized registry

Each participating Lean project hosts a `registry/` folder containing a
manifest of its published declarations. The global registry is the union
of all project-local registries — no central server required.

- **Publication** is `git push`
- **Verification** is `lake build` (Lean's kernel is the authority)
- **Consensus** is trivial: one valid proof is enough
- **Discovery** is each project's `sources.json`, the registries it consults ([usage.md](usage.md) step 6); a curated default list does not exist yet

Authors annotate their code with `@[publish]` and `@[open_point]`
attributes; `#ca_registry` (or `ca registry`) scans the environment,
computes content addresses, classifies each declaration (open / proved /
conditional / definition / axiom) and writes the registry folder during
`lake build`.
Both paths share one generation core and produce byte-identical
registries; attribute descriptions are recorded in `declarations.json`.
From the other side, `#ca_lookup` and `resolve%` read the registries
listed in `sources.json` inside Lean, and `ca lookup` reads node files
too ([usage.md](usage.md) step 6). `use`, which would bring a
declaration that is not in scope in from a node file, is not implemented.

**The registry key has two tiers.** Each entry carries `stmt`, the
exact `RefHash` statement id (base58): references are embedded by their
own ids, so it is exact down to Lean's core and changes whenever
anything in that cone changes, including a toolchain release. It also
carries `type_hash`, the *name-based* L0 hash (hex): references by
name, so it survives toolchain releases but is blind to redefinition of
the constants it mentions. Two registries match exactly on `stmt`, or
coarsely on `type_hash`; `meta.json` records the toolchain and the
encoding scheme so a consumer knows which to expect. `ref` (what a
dependent embeds) is emitted too. For an `@[open_point]` both ids are
of its *statement*, so a theorem stating the proposition literally
matches it on both tiers.

Computing `stmt` needs the ids of everything a statement mentions,
transitively down to core — the *statement cone*, which follows types
and the values of definitions but never theorem proofs. CA's modules
are precompiled, so `#ca_registry` runs compiled code during
elaboration, and the cone's imported part is cached under `.lake/ca/`
(keyed by Lean version, encoding scheme and the identity of every
imported `.olean`), so a rebuild recomputes only the project's own
declarations.

See [registry-design.md](registry-design.md) for the full registry
architecture, [registry-protocol.md](registry-protocol.md) for the
protocol between independent registries, and [README.md](README.md) for
which documents describe what exists and which describe plans.

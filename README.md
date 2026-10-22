# CA — Content-Addressing for Lean 4

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="docs/banner-dark.svg?v=3">
  <img alt="One theorem, four objects: its name is found through a namespace and lasts until renamed; its statement is found by computing it from the proposition and survives renames, moves and re-proving; its Lean proof lives in a repository; its proof term is a cache found by asking the network" src="docs/banner-light.svg?v=3" width="100%">
</picture>

### Warning: this is an early prototype, still subject to conceptual and implementation flaws and API churn.

CA gives every Lean 4 declaration an address derived from what it *is*
— its elaborated statement and, where it matters, its value, with
everything it mentions addressed the same way — rather than from its
name, file or project. Addresses are computed, not assigned: anyone can
recompute one ([`docs/spec.md`](docs/spec.md) defines the bytes), and
two projects that state the same theorem reach the same address without
coordinating.

The banner shows one theorem as the four objects formal mathematics
deals with, and the values on it are real: `ByKFv4nqHrcs…` is the
address of `Nat.add_zero`'s statement, derived byte by byte in
[docs/worked-example.md](docs/worked-example.md).

## One theorem, several objects: how each is found, what it survives

Formal mathematics handles several objects for one theorem, and for each
the useful questions are how you find it and what can change without
changing it. Every statement id hashes the same canonical form, L0: bound variables as de
Bruijn indices (α-equivalence), universe parameters renamed by position,
levels normalised, metadata stripped; hypothesis order and binder info
are kept. The ids differ in what a mentioned constant becomes — its
**name** or its own **id** — and in whether the proof is included.

| object · id | what it hashes | found by | stable under | changes when | blind to |
|---|---|---|---|---|---|
| name | nothing: a pointer in a namespace | asking whoever owns the namespace | until its owner renames it | the owner's decision | content, by design |
| statement · `stmt` | the statement, references by **id** | computing it from the proposition: no need to know who proved it, or where | renaming or moving the theorem *or anything it mentions*, re-proving, α-renaming, universe renaming | shape, hypothesis order or binder info; any type or definition value in its cone, including Lean's core across releases | nothing in its cone; definitionally equal reformulations stay distinct |
| reference · `ref` | `stmt` for a theorem, `decl` for anything else | as `stmt`, or as `decl` | theorem: as `stmt`; definition: renaming, moving | theorem: as `stmt`; definition: its value or its value's cone | — |
| coarse statement · `type_hash` | the statement, references by **name** | computing it, as a candidate across toolchains | renaming or moving the theorem, re-proving, α- and universe renaming, toolchain releases | shape, order, binder info; a mentioned name is renamed | redefinition behind an unchanged name |
| Lean proof | the proof text | the repository that holds it | nothing beyond itself | any edit or context change | what it elaborates to |
| proof term · `decl` | the whole declaration, proof or value included | asking the network for witnesses of the `stmt` | renaming, moving | for a theorem, its proof term: a tactic, Mathlib or the elaborator can change it with identical source | — |
| compiled module · `.olean` | a whole module | the build that produced it | nothing | any declaration in it, or the toolchain | — |

Three rules follow, and the rest of CA is built on them:

- **What must survive rewriting a proof keys on `ref`**, which for a
  theorem is its `stmt`: citations, dependency edges, assumptions of a
  relative verification, annotations. Re-proving a theorem changes
  nothing downstream; changing a definition's value changes everything
  that could unfold it.
- **Only `type_hash` survives a toolchain release**, and only as a hint.
  Exact ids embed their dependencies' ids, so a change in Lean's core
  propagates upward: on the v4.33 → v4.35 bump about three quarters of a
  Mathlib sample changed `decl`. A coarse match is a candidate to
  confirm, never proof that two libraries mean the same thing.
- **`decl` and `.olean` are caches**, not identities anyone should cite.

The full table, with bindings and verification records, is in
[docs/ref-hash.md](docs/ref-hash.md#which-id-to-use-where-what-each-is-stable-under).

## What it is for

The unit a mathematician cares about is a result, not a file. CA makes
that unit addressable, which is what the following need:

- **Referencing a result you cannot locate.** You know the statement;
  you do not know the repository, package, module or revision that
  holds it. A statement id is computable from the proposition alone, by
  anyone, without knowing who proved it.
- **Asking "has this already been proved?"** Two libraries that prove
  the same theorem produce the same statement id, so duplication is a
  lookup rather than a literature search. This is the question an agent
  must answer both before starting work and before offering it back.
- **Citing across refactors.** Renaming a declaration, moving it
  between files, reorganising namespaces, or renaming anything it
  references leaves its address unchanged.
- **Knowing when a statement was weakened.** Because a reference is
  embedded by *its own* address, a redefined constant produces a
  different statement id. "This proves the same thing it did before" is
  a comparison of two hashes.
- **Alternative proofs as first-class objects.** Two proofs of one
  theorem share a statement id and differ in their declaration id, so a
  store can hold both instead of overwriting one with the other.
- **Incremental work that stops where mathematics stops.** Since a
  dependent embeds a theorem's *statement*, re-proving a theorem
  invalidates nothing downstream; changing a definition's value
  invalidates everything that could unfold it.
- **Metadata that follows the statement.** A LaTeX rendering, a prose
  description or a translation belongs to a statement, not to a file
  path — keyed by statement id it is written once and shared by every
  proof of it and every project that uses it.
- **Decentralised publication.** Addresses are computed, not assigned:
  no registrar, no coordination, and anyone can verify by re-hashing.

CA is the addressing layer only. Building a store, a verifier or a
registry on top of it is a separate concern — see [Scope and related work](docs/scope.md).

## The identity: three ids per declaration

`CA.RefHash` computes, for every declaration, three ids over canonical
serialisations in which each referenced constant is replaced by its own
id (names never enter) and mutual or inductive families are hashed as
one strongly connected component:

| id | of what | answers |
|----|---------|---------|
| `stmt` | the type, with universe arity | *what does this claim?* |
| `decl` | the whole `ConstantInfo` — kind, flags, type, value, structural fields | *which declaration is this, exactly?* |
| `ref` | `stmt` for theorems, `decl` otherwise | *what may a dependent rely on?* |

`ref` is the interesting one. A dependent of a theorem can observe only
its statement — by proof irrelevance no term can distinguish two proofs
of one proposition — while a dependent of a definition may unfold it.
Embedding `ref` therefore makes identity propagate exactly as far as
mathematical dependence does.

See [`docs/ref-hash.md`](docs/ref-hash.md) for the full construction,
and `lake exe refhash-test` for the properties it is tested against
(α-renaming invariance, proof irrelevance, value sensitivity, blocks,
determinism, order independence).

## How it works

### Content addressing

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
version-spanning handle, and the registry emits both (see below). An intermediate "content-based" mode, which embedded the
referenced declaration's *type* hash, was removed before v0.1.0.

See [docs/address.md](docs/address.md) for the full addressing design.

### Decentralized registry

Each participating Lean project hosts a `registry/` folder containing a
manifest of its published declarations. The global registry is the union
of all project-local registries — no central server required.

- **Publication** is `git push`
- **Verification** is `lake build` (Lean's kernel is the authority)
- **Consensus** is trivial: one valid proof is enough
- **Discovery** will be a curated `sources.json` listing known repos (not implemented yet)

Authors annotate their code with `@[publish]` and `@[open_point]`
attributes; `#ca_registry` (or `ca registry`) scans the environment,
computes content addresses, classifies each declaration (open / proved /
conditional / definition / axiom) and writes the registry folder during
`lake build`.
Both paths share one generation core and produce byte-identical
registries; attribute descriptions are recorded in `declarations.json`.
Resolution from the other side — `use`, `resolve%`, and reading other
projects' registries through `sources.json` — is designed but not yet
implemented, so today the registry is publishable but not yet
consumable.

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

See [docs/registry-design.md](docs/registry-design.md) for the full
registry architecture, and [docs/README.md](docs/README.md) for which
documents describe what exists and which describe plans.

## Documentation

| Document | What it covers |
|---|---|
| [Using CA in your project](docs/usage.md) | adding the dependency, `@[publish]` / `@[open_point]`, statuses, generating and publishing `registry/` |
| [The `ca` CLI](docs/cli.md) | `registry`, `fetch`, `address`, `selftest` |
| [Building and dependencies](docs/building.md) | the two Lake packages, Nix and Ubuntu builds, tests, toolchain and versioning |
| [Modules](docs/modules.md) | the library's modules and what each implements |
| [Scope and related work](docs/scope.md) | where CA is used, LeanArchitect, what an address covers and what it cannot (incl. the closed-term / α-equivalence caveat) |
| [Worked example](docs/worked-example.md) | the banner's address computed byte by byte |
| [RefHash](docs/ref-hash.md) | the `stmt` / `decl` / `ref` identity scheme in full |
| [Registry protocol (draft)](docs/registry-protocol.md) | the registry as a protocol between independent nodes: relative verification and derived "proved", objects, checkers and mirrors, merge, names, revocation, a SQLite file as the published node; today vs required |
| [Registry design](docs/registry-design.md) | registry format, two-tier key, what is built and what is planned |
| [All documents](docs/README.md) | index with the status of each |

Quick start: `require ca from git "https://github.com/proofinity-it/CA" @ "v0.1.0"`,
mark declarations with `@[publish]` / `@[open_point]`, and end a module with
`#ca_registry "registry/"`; `lake build` writes the registry.

## License

Copyright © 2026 Proofinity s.r.l. Licensed under the Apache License,
Version 2.0: see [LICENSE](LICENSE) and [NOTICE](NOTICE).

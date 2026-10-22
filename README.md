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

## Documentation

| Document | What it covers |
|---|---|
| [What it is for](docs/what-it-is-for.md) | the questions a result's address answers: referencing a result you cannot locate, "already proved?", citing across refactors, detecting weakened statements, alternative proofs, incremental work, metadata, decentralised publication |
| [Using CA in your project](docs/usage.md) | adding the dependency, `@[publish]` / `@[open_point]`, statuses, generating and publishing `registry/` |
| [The `ca` CLI](docs/cli.md) | `registry`, `fetch`, `address`, `selftest` |
| [Building and dependencies](docs/building.md) | the two Lake packages, Nix and Ubuntu builds, tests, toolchain and versioning |
| [Modules](docs/modules.md) | the library's modules and what each implements |
| [Scope and related work](docs/scope.md) | where CA is used, LeanArchitect, what an address covers and what it cannot (incl. the closed-term / α-equivalence caveat) |
| [Worked example](docs/worked-example.md) | the banner's address computed byte by byte |
| [How it works](docs/how-it-works.md) | the canonicalize / serialize / hash pipeline, L0 and L1, the name-based hash, and the registry: attributes, `#ca_registry`, the two-tier key, the statement cone and its cache |
| [The identity: three ids per declaration](docs/ref-hash.md) | `stmt`, `decl`, `ref`: what each hashes and answers, why `ref` is the one a dependent embeds, blocks, scheme versions, the tested properties |
| [Registry protocol (draft)](docs/registry-protocol.md) | the registry as a protocol between independent nodes: relative verification and derived "proved", objects, checkers and mirrors, merge, names, revocation, a SQLite file as the published node; today vs required |
| [Registry design](docs/registry-design.md) | registry format, two-tier key, what is built and what is planned |
| [All documents](docs/README.md) | index with the status of each |

Quick start: `require ca from git "https://github.com/proofinity-it/CA" @ "v0.1.0"`,
mark declarations with `@[publish]` / `@[open_point]`, and end a module with
`#ca_registry "registry/"`; `lake build` writes the registry.

## License

Copyright © 2026 Proofinity s.r.l. Licensed under the Apache License,
Version 2.0: see [LICENSE](LICENSE) and [NOTICE](NOTICE).

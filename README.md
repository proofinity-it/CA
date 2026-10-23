# CA — Content-Addressing for Lean 4

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="docs/banner-dark.svg?v=3">
  <img alt="One theorem, four objects: its name is found through a namespace and lasts until renamed; its statement is found by computing it from the proposition and survives renames, moves and re-proving; its Lean proof lives in a repository; its proof term is a cache found by asking the network" src="docs/banner-light.svg?v=3" width="100%">
</picture>

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

## The registry

Addresses exist to be looked up, and the registry is where that
happens. A project marks the declarations it wants to publish, and
`lake build` writes a `registry/` folder holding, for each, its ids,
its statement (checkable without Lean), its status (open, proved, conditional, definition, axiom) and what its
status depends on. Publishing is `git push`; the kernel that built the
project is the verifier. The global registry is the union of such
folders, together with the nodes that mirror or re-check them: no
central server, no registrar. A reader with a statement in hand asks
one question, "has this been proved, by whom, under which
assumptions?", and gets the answer by id, never by name.

The protocol has two kinds of node. A **static** node is a file a
project produces and publishes by copying it, with nothing to host; a
**live** node is a working store with builds and kernel re-checks on
top that exchanges the same file ([declbuild](docs/scope.md)'s keeps
its in Redis). `ca pack` writes a project's node file and `ca check`
checks one without trusting it ([`docs/cli.md`](docs/cli.md); the format
is [`docs/payload.md`](docs/payload.md), draft 2). So does
`tools/registry_ref.py`, an independent checker in Python's standard
library written from the documents alone. Reading them back: a
project lists the registries it consults in `sources.json`; `ca lookup`
asks every one of them about a statement id, a coarse hash or a name,
`#ca_lookup` does the same inside Lean, and `resolve% "<stmt>"` is the
proof a source binds to that statement, checked against the current
environment ([`docs/usage.md`](docs/usage.md)).

Two documents propose the specifications this needs. [`docs/spec.md`](docs/spec.md)
is normative for the ids: the bytes of `stmt`, `decl` and `ref` under
scheme 1, with test vectors and an independent reimplementation.
[`docs/registry-protocol.md`](docs/registry-protocol.md) is a draft of
the protocol between independent registries: statements as first-class
objects, verification relative to stated assumptions, checkers and
mirrors, signed names, and one SQLite file as the published form of a
node. Of that protocol, the node file, its checks (`ca check`, `ca verify`
with kernel-checked, signed records), signed names and merge exist today;
the derivation of "proved" across several nodes and over trusted signers
does not yet ([`docs/plan.md`](docs/plan.md)).

## One theorem, several objects

A theorem exists as several objects: its name, its statement, the Lean
text of its proof, the proof term the elaborator produced, the compiled
module. For each, the useful questions are the same three: how do you
find it, what can change without changing it, and what changes it. CA
adds the computed ids (`stmt`, `type_hash`, `decl`); the other objects
exist anyway.

| object | how you find it | unchanged by | changed by |
|---|---|---|---|
| **name** (`Nat.add_zero`) | ask the owner of the namespace | any edit to the statement or the proof: a name says nothing about content | the owner renaming it |
| **statement id** `stmt` (CA, exact) | compute it from the proposition, without knowing who proved it or where | renaming or moving the theorem; renaming or moving anything it mentions; re-proving it; renaming bound variables or universe parameters | any change to the statement's shape, hypothesis order or binder info; any change to the type or value of a definition it mentions, or to the statement of a theorem it mentions, transitively down to Lean's core, so also a toolchain release |
| **coarse statement id** `type_hash` (CA, by name) | compute it; use it to find candidates across toolchains | everything `stmt` is unchanged by, plus toolchain releases and redefinition of anything it mentions, as long as the names stay | any change to the statement's shape, hypothesis order or binder info; renaming a constant it mentions |
| **Lean proof** (source text) | the repository that holds it | nothing | any edit to the text |
| **declaration id** `decl` (CA, proof included) | ask a store for the witnesses of a `stmt` | renaming or moving the theorem | the proof term, which a tactic, Mathlib or the elaborator can change with identical source; everything that changes `stmt` |
| **compiled module** `.olean` | the build that produced it | nothing | any declaration in the module, or the toolchain |

All three CA ids hash the same canonical form of the statement, L0:
bound variables as de Bruijn indices, universe parameters renamed by
position, levels normalised, metadata stripped; hypothesis order and
binder info are kept. They differ in two choices only: a mentioned
constant enters by its own id (`stmt`, `decl`) or by its name
(`type_hash`), and the proof is included (`decl`) or not (`stmt`,
`type_hash`). A fourth id, `ref`, is not another object but the rule
for what a dependent embeds: the `stmt` of a theorem, the `decl` of
anything else, because a dependent can observe a theorem's statement
only and a definition's value too.

Two "unchanged by" entries are weaknesses, not features: a name is
unchanged by any change of content, and `type_hash` is unchanged when a
constant it mentions is redefined behind the same name. `stmt` has a
limit of its own: two definitionally equal formulations of one theorem
are different statements and get different ids.

Three rules follow, and the rest of CA is built on them:

- **Anything that must survive rewriting a proof keys on `ref`**: a
  citation, a dependency edge, the assumption of a relative
  verification, an annotation. Re-proving a theorem changes nothing
  downstream; changing a definition's value changes everything that
  could unfold it.
- **Only `type_hash` survives a toolchain release, and only as a
  hint.** `stmt` embeds the ids of everything it mentions, so a change
  in Lean's core propagates upward: on the v4.33 to v4.35 bump about
  three quarters of a Mathlib sample changed `decl`. A `type_hash`
  match is a candidate to confirm by recomputing `stmt`, never proof
  that two libraries mean the same thing.
- **`decl` and `.olean` are caches**, not identities anyone should cite.

The full table, with bindings and verification records, is in
[docs/ref-hash.md](docs/ref-hash.md#which-id-to-use-where-what-each-is-stable-under).

## Documentation

| Document | What it covers |
|---|---|
| [What it is for](docs/what-it-is-for.md) | the questions a result's address answers: referencing a result you cannot locate, "already proved?", citing across refactors, detecting weakened statements, alternative proofs, incremental work, metadata, decentralised publication |
| [Using CA in your project](docs/usage.md) | adding the dependency, `@[publish]` / `@[open_point]`, statuses, generating and publishing `registry/` |
| [The `ca` CLI](docs/cli.md) | `registry`, `pack`, `check`, `verify`, `lookup`, `fetch-sources`, `keygen`, `merge`, `digest`, `diff`, `migrate`, `fetch`, `address`, `selftest` |
| [Building and dependencies](docs/building.md) | the three Lake packages, Nix and Ubuntu builds, tests, toolchain and versioning |
| [Modules](docs/modules.md) | the library's modules and what each implements |
| [Scope and related work](docs/scope.md) | where CA is used, LeanArchitect, what an address covers and what it cannot (incl. the closed-term / α-equivalence caveat) |
| [Worked example](docs/worked-example.md) | the banner's address computed byte by byte |
| [How it works](docs/how-it-works.md) | the canonicalize / serialize / hash pipeline, L0 and L1, the name-based hash, and the registry: attributes, `#ca_registry`, the two-tier key, the statement cone and its cache |
| [The identity: three ids per declaration](docs/ref-hash.md) | `stmt`, `decl`, `ref`: what each hashes and answers, why `ref` is the one a dependent embeds, blocks, scheme versions, the tested properties |
| [Payloads (draft)](docs/payload.md) | the stored form of a declaration in a node file: canonical units the ids are recomputed from, decorations for names, the measured size |
| [Registry protocol (draft)](docs/registry-protocol.md) | the registry as a protocol between independent nodes: relative verification and derived "proved", objects, checkers and mirrors, merge, names, revocation, a SQLite file as the published node; today vs required |
| [Registry design](docs/registry-design.md) | registry format, two-tier key, what is built and what is planned |
| [Development plan](docs/plan.md) | the seven work items, each with what it delivers and its status: consuming a node, CA as a checker, merge and reconciliation, CI and fuzzing, scale, toolchain migration, the example project |
| [Examples](examples/README.md) | two small projects: one publishes a registry (committed, readable without building), the other lists it in `sources.json` and cites a result by address with `resolve%`; a walkthrough script packs, checks, verifies, signs and merges |
| [All documents](docs/README.md) | index with the status of each |

Status: v0.3.0. The encoding scheme is versioned (`meta.json` and every
id preimage carry it), so a later scheme can coexist with this one; a
registry is publishable as a folder or as a node file; a node file is
checkable, kernel-verifiable with signed records, and mergeable; a build
can look statements up in the registries it lists. Left:
[`docs/plan.md`](docs/plan.md). The API may still change.

Quick start: `require ca from git "https://github.com/proofinity-it/CA" @ "v0.3.0"`,
mark declarations with `@[publish]` / `@[open_point]`, and end a module with
`#ca_registry "registry/"`; `lake build` writes the registry.
[`examples/publish`](examples/publish) is exactly that, and
[`examples/consume`](examples/consume) reads it.

## License

Copyright © 2026 Proofinity s.r.l. Licensed under the Apache License,
Version 2.0: see [LICENSE](LICENSE) and [NOTICE](NOTICE).

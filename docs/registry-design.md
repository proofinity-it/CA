# Decentralized Registry Design

> **Status (2026-10).** This is a design document; parts of it are built
> and parts are not. **Implemented:** `@[open_point]` / `@[publish]`,
> `#ca_registry` and `ca registry` (one generation core; status
> classification with `proves` / `proved_by` / `status_deps` and the
> within-registry cascade; files written only on change), `statements.json`
> (each entry's statement as a unit, [payload.md](payload.md)), `meta.json`
> with counts, toolchain and encoding-scheme version; the two-tier key
> (`stmt` exact, `type_hash` coarse) with the cached statement cone.
> **Not implemented:** `sources.json`, the resolution protocol (`use`,
> `resolve%`, `use!`), the registry cache, cross-project cascade and
> impact ranking, `--all` / `--dry-run` / `--level` generation flags,
> address-valued dependencies. Sections below describing those are plans.

> **See also** [registry-protocol.md](registry-protocol.md), the draft
> protocol under which this folder (packed into a file, a static node)
> and declbuild's Redis store (a live node) hold nodes of one network.
> This document describes the folder and the attributes; the
> protocol describes how nodes exchange and check what the folders and
> nodes hold.

## Overview

The global registry of formal mathematics is the union of project-local
registries. Each participating Lean project hosts a `registry/` folder
containing a manifest of its published declarations. There is
no central server — publication is `git push`, verification is `lake build`,
and discovery is a curated list of known registry-hosting repositories.

This design follows from two properties of content-addressing:

1. **Determinism.** The same mathematical content always produces the same
   address, regardless of who computes it or where.
2. **Monotonic consensus.** A declaration is proved if *any* registry has a
   valid proof. Proofs are monotonic — once proved, always proved. No
   conflict resolution protocol is needed.

## Architecture

Three pieces compose the system, all living in the `CA` repository:

1. **The content-addressing engine** (`CA.*`) — canonicalization, hashing,
   serialization. The core library that computes addresses.

2. **The registry module** (`CA.Registry.*`) — `@[publish]` and
   `@[open_point]` attributes, status classification, and the
   `#ca_registry` command (also `ca registry` in the CLI) that scans the
   environment and writes the local registry folder.

3. **The sources list** (planned) — a file listing known registry-hosting
   GitHub repositories, which resolution tools (`use`, `resolve%`, also
   planned) consult to find declarations across the ecosystem.

### Module layout

Everything lives in the `CA` repository. Downstream projects depend on
a single package:

```lean
require ca from git "https://github.com/proofinity-it/CA" @ "v0.2.0"
```

Source tree (items marked *planned* are not yet implemented):

```
CA/
├── lakefile.lean
├── CA.lean                        # re-exports all modules
├── CA/
│   ├── Canonical.lean             # L0/L1 canonicalization
│   ├── SHA256.lean                # SHA-256 (pure Lean) + Hasher hook
│   ├── RefHash.lean               # stmt / decl / ref ids
│   ├── ExprHash.lean              # Expr serialization, DeclHash, batch hashing
│   ├── Export.lean                # JSON manifest, edge list, summary stats
│   ├── Util.lean                  # collectConstants, constantKind, schemeVersion
│   └── Registry/
│       ├── Basic.lean             # entry types, extensions, query API
│       ├── Attributes.lean        # @[publish], @[open_point]
│       ├── Generate.lean          # #ca_registry: classify, JSON output
│       ├── Resolve.lean           # use, use!, resolve% elaborators (planned)
│       └── Sources.lean           # sources.json parsing, cache management (planned)
├── cli/                           # `ca` CLI: separate package (Redis, OpenSSL)
├── sources.json                   # default sources list (planned)
└── docs/
    └── ...
```

### Why a single repo

The attribute library and the content-addressing engine are tightly
coupled: `@[publish]` needs to invoke the CA hashing pipeline to generate
registry entries, and `#ca_registry` uses `CA.ExprHash`
directly. Keeping them in separate repos means version-syncing two
packages that share core logic.

A single repo with two Lake packages — the library at the root, the
CLI in `cli/` — gives both:

- **One dependency** for downstream projects (`require ca`), and a pure
  Lean one: the library has no native dependencies.
- **Separation** — the CLI's dependencies (lean4-cli, redis-lean,
  OpenSSL, hiredis) live in `cli/lakefile.lean` and are never fetched by
  a project that only `require`s the library.

### Downstream project structure

A project using the registry:

```
my-project/
├── lakefile.lean                  # requires ca
├── MyProject/
│   └── Theorems.lean              # @[publish], @[open_point] annotations
└── registry/                      # auto-generated, committed to git
    ├── declarations.json          # one entry per annotated declaration
    ├── statements.json            # each entry's statement as a unit (payload.md)
    └── meta.json                  # counts by status, toolchain, scheme version
```

Every project that opts in becomes a registry node. The global registry is
the union of all project-local registries.

## Registry Folder Format

### `meta.json`

Project-level metadata, rewritten (only when changed) on each generation.
As emitted today:

```json
{
  "project": "MyProject.Registry",
  "ca_hash_level": "L0",
  "ca_hash_mode": "name-based",
  "ca_scheme_version": 1,
  "ca_key_tiers": {
    "exact": "stmt (RefHash statement id, base58); ref = what dependents embed",
    "coarse": "type_hash (name-based L0 SHA-256, hex)"
  },
  "lean_toolchain": "leanprover/lean4:v4.35.0",
  "entries": 13,
  "open_points": 3,
  "open_points_proved": 1,
  "published": 10,
  "proved": 5,
  "conditional": 2,
  "definitions": 2,
  "axioms": 1
}
```

Planned additions: `url` (source repository), `commit` (the revision the
registry was generated from), `generated_at`, `generator_version`.

### `statements.json`

Each entry's statement as a statement unit ([payload.md](payload.md) §3)
with one decoration naming it, against one ref table and one name table
for the file:

```json
{ "payload_format": 1, "ca_scheme_version": 1,
  "refs":  ["<base58 ref id>", …],
  "names": [["Nat", "add_zero"], …],
  "statements": [{ "name": "Conj", "stmt": "ByKFv4nq…",
                   "unit": "<base64>", "decoration": "<base64>" }, …] }
```

`stmt` is recomputed from `unit` and `refs` alone, with no Lean
(`CA.Registry.checkStatementsFile`); the decoration rebuilds the type
with its names. An entry whose unit does not check to its `stmt` or does
not rebuild exactly is left out, with a warning (none in the tests).

### `declarations.json`

One entry per annotated declaration, sorted by name. As emitted today
(Lean's JSON printer orders keys alphabetically):

```json
[
  {
    "description": "a conjecture",
    "kind": "definition",
    "module": "MyProject.Theorems",
    "name": "MyProject.Conj",
    "pp_type": "∀ (n : Nat), n + 0 = n",
    "proved_by": ["MyProject.conj_literal"],
    "ref": "5PRqoKPV4WqB…",
    "status": "proved",
    "stmt": "ByKFv4nqHrcs…",
    "type_deps": ["Eq", "HAdd.hAdd", "Nat", "OfNat.ofNat", "instHAdd", "instAddNat", "instOfNatNat"],
    "type_hash": "d73f3967fc94d334…"
  },
  {
    "kind": "theorem",
    "module": "MyProject.Theorems",
    "name": "MyProject.conj_literal",
    "pp_type": "∀ (n : Nat), n + 0 = n",
    "proves": ["MyProject.Conj"],
    "ref": "ByKFv4nqHrcs…",
    "status": "proved",
    "stmt": "ByKFv4nqHrcs…",
    "type_deps": ["Eq", "HAdd.hAdd", "Nat", "OfNat.ofNat", "instHAdd", "instAddNat", "instOfNatNat"],
    "type_hash": "d73f3967fc94d334…"
  },
  {
    "kind": "theorem",
    "module": "MyProject.Theorems",
    "name": "MyProject.uses_open",
    "pp_type": "Open1 → 2 * 1 = 2",
    "ref": "…",
    "status": "conditional",
    "status_deps": ["MyProject.Open1"],
    "stmt": "…",
    "type_deps": ["Eq", "HMul.hMul", "Nat", "OfNat.ofNat", "Open1", "…"],
    "type_hash": "99d2dbc9f0bf03f4…"
  }
]
```

#### The two-tier key

| field | tier | what it is | changes when |
|---|---|---|---|
| `stmt` | exact | `RefHash` statement id (base58); for a `Prop` definition, of its *value* | anything in the statement's cone changes, down to Lean's core (so: every toolchain release that touches the cone) |
| `ref` | exact | `RefHash.ref`: `stmt` for theorems, the value-inclusive `decl` otherwise — what a dependent embeds | as `stmt`, plus the value for non-theorems |
| `type_hash` | coarse | name-based L0 SHA-256 (hex) of the same statement | the statement's shape or the *names* it mentions change |

Matching two registries: equal `stmt` is the identical statement with no
further question; otherwise equal `type_hash` is the same statement up
to the names of its references, a coarse match a consumer may accept or
verify. Within one registry the generator itself uses `stmt` (or the
open point's constant) to decide `proves`. Note that the open point
`Conj` and the theorem `conj_literal` above share `stmt` and `type_hash`
while `Conj.ref ≠ Conj.stmt` (a definition's `ref` includes its value).

`type_deps`, `status_deps`, `proves` and `proved_by` are declaration
*names*. Planned additions: address-valued dependencies, `value_deps`,
per-entry `level` / `toolchain`.

#### How `stmt` is computed at build time

`stmt` needs the `ref` of every constant the statements mention,
transitively: the **statement cone** (`statementCone`), which follows
type references always and value / structural references of
non-theorems, never theorem proofs (`RefHash.computeIds (withProofs :=
false)`; a theorem's `ref` is its `stmt`). Two things make this
affordable inside `#ca_registry`, which runs during elaboration:

- the `CA` library is built with `precompileModules`, so the command
  executes compiled code;
- the `ref`s of the *imported* part of the cone are cached under
  `.lake/ca/reftable-<key>.bin`, keyed by Lean version, encoding scheme
  and the path / size / mtime of every imported `.olean`
  (`importsCacheKey`). Only exact entries (nothing unresolved) are
  cached; the project's own declarations are recomputed every time.
  A malformed or stale file is ignored, never trusted.

`ca registry` (compiled CLI) runs the same code with the same cache, so
both paths stay byte-identical.

#### Status classification

Status is computed automatically from the environment by `#ca_registry`
/ `ca registry`:

| Pattern | Status | Rule |
|---|---|---|
| `def P : Prop := ...` with `@[open_point]`, no published proof | `open` | Explicitly marked as open problem |
| `def P : Prop := ...` with `@[open_point]`, and a published `theorem : P` (by constant or by statement address) | `proved` | `proved_by` lists the theorems; they list `P` in `proves` |
| `theorem foo : Q := proof`, no hypothesis reaching an open point | `proved` | Type-checks (the kernel is the authority) |
| `theorem bar (h : OpenP) : Q := ...`, `OpenP` still open | `conditional` | Proved modulo open hypotheses; also through Prop-valued definitions (`def W : Prop := OpenP ∧ …`) |
| same, once `OpenP` is proved in the registry | `proved` | the cascade below, within one registry |
| `@[publish] def` / `inductive` / … | `definition` | published non-theorems are not "proved" |
| `@[publish] axiom` | `axiom` | an assumption |

Hypotheses are the binder domains of the theorem's type; open points in
the conclusion (`¬ OpenP`) do not make it conditional. For conditional
declarations, `status_deps` lists the open hypotheses — the declarations
whose proof would promote this entry from conditional to proved. The
heuristic "a `Prop` with no theorem of its type is open" is *not*
implemented; open points are declared with the attribute.

#### Append-only convention (planned)

Today the generator writes the current set of annotated declarations,
sorted by name, and git history is the audit trail. The intended
convention is append-only: entries are never removed; if a declaration's
statement changes, a new entry with a new address is added and the old
one remains as history; status updates (open → proved) are the only
in-place mutation.

## Sources List (planned)

The sources list is a JSON file enumerating known registry-hosting
repositories. A default `sources.json` ships with the `CA` package; users
can override it with a project-local `sources.json`.

### `sources.json`

```json
{
  "version": 1,
  "registries": [
    {
      "name": "mathlib4",
      "url": "https://github.com/leanprover-community/mathlib4",
      "registry_path": "registry/",
      "description": "Lean 4 Mathlib"
    },
    {
      "name": "EM",
      "url": "https://github.com/marcellop71/EM",
      "registry_path": "registry/",
      "description": "Euclid-Mullin formalization"
    }
  ]
}
```

### Adding a project to the ecosystem

A project joins the global registry by:

1. Adding `require ca from git "https://github.com/proofinity-it/CA" @ "v0.2.0"`
   to its `lakefile.lean`.
2. Annotating declarations with `@[publish]` or `@[open_point]`.
3. Adding `#ca_registry "registry/"` at the end of a module (or running
   `ca registry`) to produce `registry/`.
4. Committing `registry/` to git and pushing.
5. *(planned)* Opening a PR to add one entry to `sources.json` in the CA
   repo.

Step 5 is the only coordination point. Everything else is local.

### Discovery alternatives

The static `sources.json` is the simplest approach. Alternatives for
later:

- **GitHub topic tag.** Projects tag themselves with `lean-formal-registry`.
  The tool discovers registries via GitHub API search. More automatic but
  adds a GitHub API dependency.
- **DNS-based.** A TXT record or well-known URL convention
  (`https://example.com/.well-known/lean-registry.json`). Over-engineered
  for now.

The static list is the right starting point. It can be replaced later
without changing any other part of the design.

## Resolution Protocol (planned)

When a user writes `use Nat.add_comm` or `resolve% Nat.add_comm`, the
resolution proceeds in stages:

```
1. Check local environment
   → found? done.

2. Check local registry cache (~/.lean/registry-cache/)
   → found? return address, module, source repo.

3. Fetch registry/ from known sources
   (GitHub raw file URLs or git sparse checkout)
   → merge into local cache.

4. Find matching name across all registries
   → return address, module, source repo.

5. Optionally: clone source, load .olean, import into environment
   (this is what use! does)
```

### Cache structure

The local cache aggregates declarations from all known registries into a
single queryable index:

```
~/.lean/registry-cache/
├── index.json          # merged index: name → address → source registry
├── addresses.json      # address → [names, modules, repos]
└── sources-etag.json   # HTTP ETags for cache invalidation
```

The cache is rebuilt on `registry update` (explicit) or when a resolution
misses the cache (lazy).

### Name conflicts

Two projects may define the same name with different types (different
addresses). This is not a conflict — they are different declarations.
Resolution disambiguates by source:

```
use Nat.add_comm              -- first match in sources order
use Nat.add_comm from mathlib -- explicit source qualifier
```

Two projects proving the same address under different names is also not a
conflict — they are aliases. The resolution result includes all known
aliases.

## Verification Model

Trust is optional. Every claim in the registry is independently
verifiable:

1. Clone the source project.
2. Run `lake build`.
3. If it compiles, the declarations are valid (Lean's kernel is the
   authority).
4. Re-run `#ca_registry` (or `ca registry`) and compare the output with the committed
   `registry/` folder.

No trust in the registry operator is required. A consumer who wants
maximum assurance verifies locally. A consumer who trusts the source
project can use the registry data directly.

### Proof certificates

For lightweight verification without a full `lake build`, a future
extension could include proof certificates — serialized proof terms or
.olean fragments that Lean's kernel can check independently. This is
not needed for the initial design.

## Status Cascade

When a proof is submitted for an open point, conditional declarations
downstream may become unconditional.

**Within one registry (implemented).** `classify` marks an open point
`proved` when a *published* theorem proves it — its type is the open
point's constant, or its type's address equals the open point's
statement address — and records the provers in `proved_by`. A
theorem's `status_deps` are the open points reached from its hypotheses
(through Prop-valued definitions too); it is `conditional` while any of
them is still open and `proved` once all have proofs in the registry.
Unpublished theorems are not scanned: a proof enters the registry by
being `@[publish]`ed.

**Across registries (planned).** A consumer merging several registries
applies the same rule to the union: an open point in project A proved in
project B promotes conditional entries in project C.

### Cross-project cascade example

```
Project A:  DeterministicStabilityLemma          → status: open
Project B:  proof_of_dsl : DSL := ...            → status: proved (proves A's open point)
Project C:  full_chain (h : DSL) : MC := ...     → status: conditional (depends on A's address)
```

A consumer merging all three registries sees:

1. A's address is proved (B has a proof).
2. C's `status_deps` are all proved.
3. C is promoted to proved.

No coordination between A, B, and C is needed. The cascade emerges from
the union of their registries.

## Impact Metric (planned)

Impact is computable from the merged dependency graph:

- The **impact** of an open point is the number of conditional declarations
  (transitively) downstream of it.
- Proving a high-impact open point cascades to close the most chains.
- `registry work --sort impact` (planned) would rank open points by impact.

This is a pure graph computation on the merged registry data. No special
infrastructure is needed.

## Lean Version Handling

Content addresses depend on normalization behavior, which could change
across Lean versions. The registry handles this by:

- Every registry's `meta.json` records `lean_toolchain`, `ca_hash_level`
  and `ca_scheme_version` (per-entry `toolchain` / `level` fields are
  planned).
- L0 addresses are pure (no MetaM) and extremely stable across versions.
  These are the safest for cross-version references.
- L1 addresses depend on `whnf` behavior. If Lean changes `whnf`, L1
  addresses may change. The registry treats different toolchain versions
  as potentially producing different addresses for the same declaration.
- Every `meta.json` records `lean_toolchain` and `ca_scheme_version`
  (the encoding scheme; a bump means ids changed, see `CHANGELOG.md`).
  Re-indexing on upgrades is a rebuild: `#ca_registry` recomputes all
  addresses.

## Generation

Two entry points share one core (`CA.Registry.generateRegistryCore`) and
produce byte-identical files:

- **`#ca_registry "registry/"`**, a command placed at the end of a
  module. It runs whenever that module is elaborated — during
  `lake build` and in the editor — and rewrites `declarations.json` /
  `meta.json` only when their content changed, so a committed registry
  does not churn.
- **`ca registry -m MyProject.Registry -o registry/`**, the CLI
  subcommand (`cli/`), for environments where the binary shares the
  project's toolchain and search path.

Both:

1. load (or are given) the elaborated environment;
2. collect the `@[publish]` and `@[open_point]` declarations;
3. compute each entry's address (name-based L0 hash of the statement);
4. classify status (see *Status classification*);
5. write the two files.

Not implemented: `--all` (publish every declaration), `--dry-run`,
`--level 1` (reducible-transparency normalisation of statements).

### When to run

`#ca_registry` makes generation part of the build: the registry is
regenerated whenever the registry module is rebuilt, which Lake does
whenever an upstream module it imports changed. A CI job that runs
`lake build` and fails on a dirty `registry/` keeps the committed
registry honest.

## Summary

| Aspect | Design |
|---|---|
| **Storage** | `registry/` folder in each project's git repo |
| **Publication** | `git push` |
| **Verification** | `lake build` (Lean's kernel) |
| **Discovery** | Static `sources.json` listing known repos (planned) |
| **Resolution** | `use` / `resolve%` queries local cache, fetches from sources on miss (planned) |
| **Consensus** | Monotonic: one valid proof is enough |
| **Coordination** | Minimal: PR to add one line to `sources.json` (planned) |
| **Cascade** | Within one registry: implemented. Across registries: emerges from the union, computed locally (planned) |
| **Versioning** | Toolchain and encoding scheme recorded per registry (`meta.json`); the name-based L0 hash is stable across versions |

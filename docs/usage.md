# Using CA in your project

This section explains how to use CA in your own Lean project to annotate
theorems and participate in the decentralized registry.

## Step 1: Add the dependency

In your project's `lakefile.lean`:

```lean
require ca from git
  "https://github.com/proofinity-it/CA" @ "v0.1.0"
```

Tags are release versions (the current release builds on Lean
`v4.35.0`; see `lean-toolchain`); use `@ "main"` if you are following
development.

Then fetch dependencies:

```bash
lake update
lake build
```

## Step 2: Annotate your declarations

Import `CA` in any `.lean` file where you want to annotate declarations:

```lean
import CA
```

Use `@[open_point]` to mark a `Prop` definition as an open problem — a
mathematical statement that you are publishing without a proof:

```lean
@[open_point "Bertrand's postulate, elementary form"]
def BertrandPostulate : Prop :=            -- Nat.Prime is from Mathlib
  ∀ n : Nat, n ≥ 1 → ∃ p, Nat.Prime p ∧ n < p ∧ p < 2 * n
```

Use `@[publish]` to mark any declaration (theorem, definition, axiom) for
publication to the registry:

```lean
@[publish "Commutativity of addition over naturals"]
theorem my_add_comm : ∀ a b : Nat, a + b = b + a := Nat.add_comm
```

A theorem with an open point among its hypotheses is automatically
classified as **conditional** — proved modulo unproved hypotheses:

```lean
@[publish "Consequence of Bertrand's postulate"]
theorem prime_between (n : Nat) (h : BertrandPostulate) (hn : n ≥ 1) :
    ∃ p, Nat.Prime p ∧ n < p ∧ p < 2 * n :=
  h n hn
```

#### What the registry records

One entry per annotated name, with a `status`:

| status | meaning |
|---|---|
| `open` | an `@[open_point]` that no published theorem in this registry proves |
| `proved` | a theorem none of whose hypotheses reaches a still-open point; or an open point that a published theorem proves (listed in `proved_by`) |
| `conditional` | a theorem with a hypothesis that reaches a still-open point (listed in `status_deps`) |
| `definition` | a published definition, inductive, constructor, … |
| `axiom` | a published axiom (an assumption, never "proved") |

A published theorem **proves** an open point when its type is that
constant, or when its type's address equals the open point's statement
address, so stating the proposition literally counts; the theorem lists
the open point in `proves`. **Hypotheses** are the binder domains of the
theorem's type; one reaches an open point directly or through the values
of Prop-valued definitions (`def Wrap : Prop := Conj ∧ True`). Open
points in the *conclusion* (`¬ Conj`, `Conj ∨ True`) do not make a
theorem conditional. Once every open point in a theorem's `status_deps`
is proved in the registry, the theorem is `proved` too. A name carrying
both attributes is one open point.

`lake exe registry-test` checks each of these rules.

#### Retroactive annotation

You can annotate declarations from other files or even upstream
dependencies without modifying their source:

```lean
import CA
import MyProject.Theorems

attribute [open_point "My conjecture"] MyProject.SomeConjecture
attribute [publish "Key lemma"] MyProject.some_lemma
```

## Step 3: Query annotations

You can inspect which declarations are annotated in the current
environment:

```lean
open CA.Registry Lean in

-- Check individual declarations
#eval isOpenPoint (← getEnv) `BertrandPostulate       -- true
#eval isPublished (← getEnv) `my_add_comm             -- true

-- List all annotated declarations
#eval getOpenPoints (← getEnv)
#eval getPublished (← getEnv)
```

## Step 4: Generate the registry folder

Add `#ca_registry "registry/"` at the end of your registry file. The
registry is generated automatically during `lake build` — no separate
command or external binary needed:

```lean
import CA
import MyProject.Theorems

attribute [open_point] MyProject.SomeConjecture
attribute [publish] MyProject.some_lemma

#ca_registry "registry/"
```

When `lake build` compiles this file, it writes (and afterwards rewrites
only when the content changes, so a committed registry does not churn):

```
my-project/
└── registry/
    ├── declarations.json    # per declaration: stmt + ref (exact), type_hash (coarse),
    │                        #   name, status, type, deps, proves / proved_by / status_deps
    ├── statements.json      # per declaration: its statement as a unit (docs/payload.md),
    │                        #   from which anyone recomputes stmt without Lean
    └── meta.json            # counts by status, toolchain, encoding-scheme version
```

## Step 5: Publish

Commit the `registry/` folder to your git repo and push. Your
declarations are now published under their content addresses, and
anyone who clones the repository can verify them by rebuilding and
regenerating the registry (`declarations.json` must come out identical).
Checking a statement does not even need that: each unit in
`statements.json` recomputes its `stmt` from its own bytes and the
file's ref table (`CA.Registry.checkStatementsFile`).

Discovery and resolution — a `sources.json` of known registries, and
`use` / `resolve%` to bring a declaration into scope by address — are
designed in [registry-design.md](registry-design.md) but not
implemented, so there is nothing to register your project with today.
Until then a registry is consumed by reading its `declarations.json`.

## What your project looks like

```
my-project/
├── lakefile.lean                  # require ca from git "..." @ "v0.1.0"
├── MyProject/
│   ├── Definitions.lean           # @[open_point] annotations
│   ├── Theorems.lean              # @[publish] annotations
│   └── Registry.lean              # retroactive annotations, #ca_registry "registry/"
└── registry/                      # generated during lake build, committed to git
    ├── declarations.json
    ├── statements.json
    └── meta.json
```

## Summary of the workflow

| Step | What you do | What happens |
|------|-------------|--------------|
| 1 | Add `require ca` to `lakefile.lean` | CA library available in your project |
| 2 | Add `@[publish]` / `@[open_point]` to declarations | Declarations marked for the registry |
| 3 | Add `#ca_registry "registry/"` to your registry file | Registry generated during `lake build` |
| 4 | `git add registry/ && git push` | Your registry is published (discovery tooling pending) |

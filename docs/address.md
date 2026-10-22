# Content Addressing

> **Scope note (2026-08).** This document describes the `address`
> subcommand and the *name-based* hash it computes (the registry's
> `type_hash`). The identity scheme CA now recommends — the three ids
> `stmt` / `decl` / `ref`, in which references are embedded by their
> own ids and mutual/inductive families hash as one SCC — is
> [`ref-hash.md`](ref-hash.md). Read that first if you are looking for
> "what is a declaration's address"; read this one for the
> canonicalisation levels (shared by both) and for the batch tooling.

The `address` subcommand computes a content address for every declaration in the environment. A content address identifies a declaration by its mathematical content rather than its human-chosen name. Two declarations with different names but identical mathematical content receive the same address.

## Overview

The address of a declaration is computed in two stages:

1. **Canonicalization** — reduce the expression to a canonical form that erases irrelevant differences
2. **Hashing** — compute a deterministic hash of the canonical expression

The result is a hex-encoded SHA-256 (256-bit) address for the type (and optionally the value) of each declaration. The JSON manifest records `hash_mode: "name_based"`.

## Stage 1: Canonicalization

Canonicalization transforms an `Expr` so that expressions that differ only in irrelevant ways become identical. Two levels are available.

### Level 0 (default)

Level 0 is pure (no `MetaM`) and ensures alpha-equivalence:

- **Universe parameter renaming.** Universe parameters are renamed to positional indices (`u_0`, `u_1`, ...) based on first-occurrence order in the expression. This ensures `theorem foo.{u, v} : ...` and `theorem bar.{α, β} : ...` with the same body get the same address. (`RefHash` instead renames a declaration's parameters positionally from its `levelParams` binder list, which additionally keeps the binder *order* and the type↔value parameter correlation — see [`ref-hash.md`](ref-hash.md).)
- **Universe level normalisation.** Every level is put in `Level.normalize` normal form after renaming, so definitionally equal levels (`max u v` / `max v u`) hash alike.
- **Metadata stripping.** `.mdata` annotations are removed. These carry source-location and elaboration metadata that is irrelevant to mathematical content.
- **Binder names.** Lean 4 `Expr` uses de Bruijn indices for bound variables and the hashed terms are *closed* (a declaration's type or value), so α-equivalence is handled by the representation: two closed terms are α-equivalent exactly when their de Bruijn trees are equal. Binder names do not affect the hash. (This holds for closed terms only; hashing open fragments modulo α is a different problem — see *What an address covers* in [scope.md](scope.md).)

### Level 1

Level 1 extends Level 0 with reducible-transparency normalization (requires `MetaM`):

- **Reducible unfolding.** All `@[reducible]` definitions are unfolded.
- **Beta-reduction.** Function applications `(fun x => body) arg` are reduced.
- **Iota-reduction.** Match/recursor applications are reduced.
- **Zeta-reduction.** Let bindings are substituted away.

Normalization uses `whnf` at every subexpression under `TransparencyMode.reducible`. This collapses type-level abbreviations and reducible definitions to the same canonical form.

Instance arguments (typically `@[semireducible]` or `@[instance]`) are **not** unfolded under reducible transparency, which is the correct behavior — `Add Nat` stays as `Add Nat`.

## Stage 2: Hashing

After canonicalization, the expression is serialized into a `ByteArray` with a unique tag byte per `Expr` constructor followed by the serialized children. The serialization:

- Tags each `Expr` constructor with a distinct byte (`.bvar` → `0x01`, `.const` → `0x05`, `.app` → `0x06`, etc.)
- Ignores binder names (they are not mathematically significant)
- Strips `.mdata` transparently
- Includes `BinderInfo` (default, implicit, strict implicit, instance implicit) in lambda and forall serializations
- Encodes `Nat` literals as length-prefixed big-endian bytes at full precision (scheme 1; scheme 0 truncated them to 64 bits)

The serialized bytes are then hashed with SHA-256 (pure Lean `sha256Pure` in the library; the CLI uses OpenSSL for speed, same digests) and formatted as a 64-character hexadecimal string, providing robust collision resistance for large corpora.

### References

A `.const name levels` node is serialized with the declaration's *name*.
This makes the hash stable across toolchains and cheap to compute, and
blind to what the name denotes; it is the coarse tier of the registry
key. Name-free identity, with references embedded by their own ids, is
`CA.RefHash` ([`ref-hash.md`](ref-hash.md)). An intermediate
"content-based" mode that embedded the referenced declaration's *type*
hash in topological order existed during development and was removed before v0.1.0: it
collided every definition of a given type and fell back to names
silently when the order did not cover a dependency.

## Proof irrelevance

For theorems (declarations in `Prop`), all proofs are definitionally equal. The value address is set to the sentinel `PROOF_IRRELEVANT` rather than hashing the proof term. This means a theorem's identity is determined entirely by its type address — what it proves, not how.

## Output

The `address` subcommand produces:

- **JSON manifest** (`manifest.json` by default) — contains metadata (toolchain, transparency, hash mode) and an array of declaration records, each with `name`, `kind`, `type_hash`, `value_hash`, `type_deps`, `value_deps`.
- **Edge list** (optional, `--edges` flag) — TSV of `source_type_hash → target_type_hash` edges for graph analysis.
- **Redis storage** — each declaration's address data is stored in `ca:decl:{name}` with fields `addr_type`, `addr_value`, `addr_type_deps`, `addr_value_deps`.

## Usage

```bash
# Default: level 0, name-based (all declarations)
ca address

# Level 1 canonicalization
ca address --level 1

# Custom output paths
ca address --output hashes.json --edges edges.tsv

# Single declaration lookup
ca address --name Nat.add_comm
ca address --name Nat.add_comm --level 1 -m Mathlib.Data.Nat.Defs
```

When `--name` is provided, the command computes the address for just that declaration, prints it, stores it to Redis, and exits without writing a manifest file.

## Source modules

| Module | Role |
|--------|------|
| `CA.Canonical` | Canonicalization (L0 pure, L1 MetaM) |
| `CA.SHA256` | Pure-Lean SHA-256, the `Hasher` hook, hex formatting (OpenSSL binding: `cli/`) |
| `CA.ExprHash` | Expr serialization, `DeclHash` structure, batch computation |
| `CA.Export` | JSON manifest, edge list, summary statistics |
| `CA.Util` | `collectConstants`, `constantKind` helpers |

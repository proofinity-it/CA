# Registry protocol, version 1 (draft)

> **Status (2026-10-22): draft for discussion.** This document specifies
> the registry as a protocol between independent nodes: what objects
> exist, which id each is known by and what that id is stable under, how
> a node checks an object it receives, how nodes merge, how a theorem
> comes to count as proved, who may write a name, how a claim is
> retracted, and how nodes find what they lack. Section 14 compares it
> item by item with what declbuild's Redis network does today. Nothing
> here is implemented in CA yet.

## 0. Why a protocol, and why here

There are currently two registries that do not know about each other:

- **CA's registry folder.** A project's `#ca_registry` writes
  `registry/declarations.json` and `meta.json`
  ([registry-design.md](registry-design.md)), published by `git push`:
  ids and statuses, no payloads.
- **declbuild's Redis network.** Every Redis instance holding
  declbuild's key schema is a node; `declbuild publish` and
  `declbuild peer push/pull` copy keys between nodes. It carries
  payloads, dependency edges, bindings and signed verification records.

Both are views of one thing: a set of content-addressed objects whose
ids are CA's. The rules that make a federation coherent are rules about
those ids, so they belong next to the ids, in CA. declbuild is one
implementation and Redis one transport; a static file layout, which
CA's registry folder grows into, is another.

## 1. Principles

- **The network is the registry; no node is complete.** Nodes hold what
  their owners care about. Proofinity's and other maintained nodes try
  to cover as much as they can; nobody is required to. A question a
  node cannot answer is asked of other nodes (section 10), not solved by
  replicating everything.
- **The statement is the unit.** Three layers are kept apart:

  | layer | known by | stable under |
  |---|---|---|
  | the **statement** of a theorem | `stmt`, canonical | renames and moves of it and of anything it mentions, re-proving, re-elaboration |
  | its **Lean proof** (source) | a fingerprint, a hint only | nothing beyond its exact text and import context |
  | its **proof term** (what an `.olean` holds) | `decl` | renames and moves only: a tactic, Mathlib or the elaborator change it, often with identical source |

  CA names statements. A node may hold a statement with no proof at all
  (an open point, or a theorem proved elsewhere). Proofs are
  **witnesses** of statements: several may exist, none is canonical,
  and two witnesses of one statement are never in conflict.
- **Nothing downstream depends on a proof.** A dependent embeds a
  theorem's `ref`, which is its `stmt`. So a proof can be checked
  *relative to* the statements it uses, treated as axioms — a global,
  content-addressed `sorry` — and whether a theorem is proved is
  *derived* from records that compose (section 5).
- **The kernel is the authority, not the network.** The protocol
  guarantees integrity (an object is what its key says) and attribution
  (a claim says who made it). Whether a proof type-checks is decided by
  a kernel run, and recorded as a signed claim.
- **A node's state is a join-semilattice.** Merging two nodes is a
  per-key join: commutative, associative, idempotent. Sync is order-free
  and replay-safe.

## 2. Identities and what they are stable under

L0 is a canonical form (de Bruijn indices, universe parameters renamed
by position, levels normalised, `mdata` stripped; hypothesis order and
binder info kept). Every statement id hashes the L0 form; they differ in
what a mentioned constant becomes: its **name** (`type_hash`) or its own
**id** (`stmt`). The full table, with what each id is blind to, is in
[ref-hash.md](ref-hash.md#which-id-to-use-where-what-each-is-stable-under):

| id | stable under | changes when |
|---|---|---|
| `type_hash` (refs by name) | renaming/moving the declaration, re-proving, toolchain releases | shape, hypothesis order, binder info; a mentioned name is renamed — and it is **blind** to redefinition behind an unchanged name |
| `stmt` (refs by id) | the above, plus renaming/moving anything it mentions | shape, order, binder info; any type or definition value in its cone, including core across releases; scheme bump |
| `ref` | theorem: as `stmt`; definition: renaming/moving | theorem: as `stmt`; definition: its value or its value's cone |
| `decl` | renaming, moving | for a theorem, its proof term |
| witness / source fingerprint | nothing beyond itself | any edit or context change |

The protocol's rule, read off the "stable under" column:

- **Everything that composes keys on `ref`** (for a theorem: `stmt`):
  dependency edges, assumptions of relative verifications, the
  derivation of "proved", statement-level annotations.
- **`type_hash` is a hint only**: discovery and cross-toolchain
  candidates. A coarse match never discharges an assumption. Why: two
  libraries defining `IsSolvable` differently give
  `theorem t : IsSolvable G` one `type_hash`; a witness from one would
  "discharge" an assumption made in the other without any kernel check
  failing.
- **`decl` and `.olean` are caches and verification keys**, not ids a
  user cites.

## 3. Objects

| object | key | content | merge |
|---|---|---|---|
| **Statement** | `stmt` | the type of a theorem in L0 form, with level parameters; carried with its definitional cone (section 4) | identical bytes under identical key |
| **Definition** (any non-theorem: def, inductive, constructor, recursor, axiom, opaque, quotient) | `decl` (= its `ref`) | the serialised `ConstantInfo`, kind, `stmt`, dependency set (ref ids) | identical bytes under identical key; a differing payload under one key is a *fault* |
| **Witness** | `decl` of a theorem | the serialised `ConstantInfo` including the proof term; its `stmt`; its dependency set (ref ids); toolchain; hints: source fingerprint, module, name | identical bytes under identical key |
| **Witness set** | `stmt` | set of `decl` ids that are witnesses of it | union |
| **Reverse dependencies** | `ref` | set of `decl` ids that reference it | union (derived; may be recomputed rather than synced) |
| **Verification record** | (`decl`, record digest) | that a kernel check of `decl` ran, and **relative to what**: `assumes` (ref ids treated as axioms), `axioms` (base axioms used, e.g. `Classical.choice`), toolchain, policy, signer, signature | union; retracted only by tombstone |
| **Binding** | (namespace, name) | the `decl` or `stmt` the name resolves to, a sequence number, the owner's signature | signed register, highest sequence number wins (section 7) |
| **Namespace claim** | namespace | owner key, delegate keys, signature | first valid claim per namespace id |
| **Tombstone** | (target, signer) | retracts a verification record or revokes a key; signed | union; wins over its target (section 8) |
| **Annotation** | `stmt`, `ref` or `decl` | renderings, descriptions, translations; attributed, optionally signed | union |
| **Auxiliary** | (namespace, auxiliary name) | `decl` of a compiler auxiliary; resolvable, never listed | as Binding |
| **Compression dictionary** | content tag | a zstd dictionary that payloads cite | identical bytes under identical key |

Non-content metadata (source text, pretty-printed type, module) travels
as **hints**: never part of a key, droppable, and conflicting hints are
all kept, attributed.

## 4. Validity on receipt

A node **must not** store an object under a content key it has not
checked.

- **Statement.** Recompute `stmt` from the type
  (`CA.RefHash.stmtIdOf`). This needs the `ref` of every constant the
  type mentions, transitively through definition values — the
  *statement cone*, which never contains a proof term. Every node can
  afford this check; it is the same computation `#ca_registry` does.
- **Definition.** Recompute `decl`, `stmt` and `ref` from the payload
  (`CA.RefHash.computeIds`), which needs the payload's cone.
- **Witness.** Recompute `decl` and `stmt` from the payload. Only nodes
  that choose to hold proofs receive witnesses; the cost of checking a
  proof term's id is paid only where the proof is kept.
- Objects whose cone is not yet present are held **pending**, not stored
  and not served. Senders transfer foundations first.
- **Witness set member.** The witness must be stored and have the set's
  `stmt`.
- **Verification record, Binding, Namespace claim, Tombstone.** The
  signature must verify and the signer must be authorised (section 7).
  Unsigned records are accepted as unsigned, or refused, by node policy.
- **Dictionary.** Recompute the content tag.

A content-id check is not a kernel check: it proves the object is what
its key says, not that a proof is correct. That is what verification
records are for.

## 5. Relative verification and "proved"

A verification record says: *witness `decl` of statement `stmt` was
kernel-checked, with the refs in `assumes` replaced by axioms of their
type and the base axioms in `axioms` accepted.* declbuild's
`verify-relative` produces exactly this: the trust set becomes axioms,
the target is checked by the stock Lean kernel.

What may be assumed follows `ref`: a theorem is assumed by its `stmt`
(its proof is never needed), a definition by its `decl` (reduction needs
its value). An assumption is therefore always a ref id, unambiguous
across projects and names.

**"Proved" is derived, not stored.** Given a set of trusted signers and
accepted base axioms, a statement S is *proved* if some witness of S
has a trusted record whose every assumption is

- a definition (its `decl` is part of the statement's meaning, not an
  open claim), or
- a statement that is itself proved, recursively, with no cycle.

S is *conditional on* {S₁, …} when that recursion bottoms out in
statements with no proved witness; S is *open* when it has no witness
with a trusted record. These are the statuses of CA's registry folder
(`proved` / `conditional` / `open`), now with kernel checks and
signatures behind them, and computable across nodes:

- Discharging S₁ anywhere in the network promotes everything verified
  relative to S₁, **without re-checking it**. This is the cross-project
  cascade.
- Two witnesses of S checked relative to different assumptions are both
  kept; S is proved if either chain closes.
- The derivation is a reader's computation over records it trusts. Two
  readers with different trusted signers may disagree, by design.

Within one toolchain this composes exactly. Across toolchains `stmt`
values differ for anything whose cone moved; a record from one
toolchain discharges an assumption from another only through an
explicit equivalence (a proved `A ↔ B`, itself a witness), never through
a `type_hash` match.

## 6. Merge

Per-key joins as in section 3, plus:

- **Fault.** Two different payloads under one content key means one
  failed section 4. A checking node never stores the wrong one; it keeps
  its own and records the peer as faulty.
- **Twins.** Declarations equal up to renaming share one `decl` and one
  canonical payload; a second publisher's payload under its own names is
  a named variant of the same object, keyed by (`decl`, name)
  (declbuild's `cinfo-named:`), not a competitor.

## 7. Names: namespaces, bindings, authority

Names are the only mutable part of the registry. The protocol makes
contention impossible by making every name belong to exactly one key.

- A **namespace id** is `label@key`, `key` the owner's base58 Ed25519
  public key (`em@2N68kx…`). Two publishers choosing one label get two
  namespaces; short labels are client-side aliases.
- A **Namespace claim** is signed by `key` and may list delegate keys.
  Only the owner can make one, since the id contains the key.
- A **Binding** `(ns, name) ↦ id` carries a sequence number and a
  signature by the owner or a delegate. Merge keeps the highest sequence
  number; ties break on signature bytes. Any two nodes that have seen
  the same bindings agree, whatever the order. Unbinding is a binding to
  the empty id with a higher number.

A node can therefore accept bindings from anyone and mirror names from
untrusted peers safely.

## 8. Revocation

- A **record tombstone** names a verification record by digest, signed
  by that record's signer; readers treat the record as absent, and the
  derivation of section 5 changes accordingly.
- A **key revocation** names a key and a time, signed by the key or a
  pre-declared revocation key; that key's later records count as
  unsigned.
- Tombstones are grow-only and never retracted.

## 9. Schemes and toolchains

- Every node manifest declares the scheme version(s) it stores; every
  object is under exactly one scheme; peers **must not** merge across
  schemes. A node may keep several schemes as separate keyspaces.
- Toolchains need no special handling: they give different ids for
  anything whose cone changed and identical ids otherwise. `type_hash`
  travels as a hint on Statements and Witnesses for cross-toolchain
  discovery.

## 10. Asking the network

Because no node is complete, the basic operations are queries that a
node answers if it can and otherwise forwards or reports as unknown:

| query | answer |
|---|---|
| statement `stmt` | the Statement, with its cone on request |
| witnesses of `stmt` | witness `decl` ids, toolchain, record summaries |
| records for `decl` | verification records (signed, with `assumes`) |
| who depends on `ref` | reverse dependencies the node knows |
| resolve `(ns, name)` | the current binding |
| candidates for `type_hash` | statements with that coarse hash (hints only) |

A reader computing whether S is proved (section 5) issues these against
the nodes in its sources list (section 11), in order, caching answers;
it never needs any node to hold everything. Lazy fetch during a check or
build is the same mechanism.

**Sync**, when a node does want to replicate, is the same union:

- **Selectors** name what to copy: everything; the cone of some roots;
  a namespace; a module prefix; the statements only of a cone (cheap,
  proof-free); the witnesses of a statement.
- **Difference finding** for large selectors exchanges summaries of
  sorted id lists and recurses only into ranges that differ (range-based
  reconciliation, or a Merkle tree over sorted ids; declbuild's
  `graph:decls` is already sorted). Small selectors exchange plain id
  lists.
- Transfer is foundations first, interruptible and replayable.

## 11. Discovery and the node manifest

- A **node manifest** is a small signed document a node serves:
  transports and URLs, schemes, namespaces held or mirrored, coverage
  hints (module prefixes, counts, whether it holds witnesses or only
  statements), policy (accepts unsigned records, read-only or not).
- A **sources list** is a list of manifests, or URLs serving them, with
  the expected key for each. CA's planned `sources.json` is exactly
  this. A reader merges the lists it trusts.

## 12. Transports

- **Redis (today).** A node is a Redis instance; objects map to a subset
  of declbuild's key schema (`cinfo:`, `ids:`, `deps:`, `stmt:`,
  `rdeps:`, `verifications:`, `bind:`, `aux:`, `meta:zstd-dict:`).
  declbuild's project state, daemon queues and `graph:*` compactions are
  local and never synced. Fast; inside a trust boundary, since Redis has
  no per-key authorisation.
- **Static files (to build).** A read-only node as a directory over HTTP
  or in git: `manifest.json`, one file per object named by its key, and
  CA's `declarations.json` as the human-readable index. Publication is
  `git push`; any web host is a public mirror. CA's registry folder
  becomes this by adding statements, optional witnesses and the
  manifest.
- **Gateway (if needed).** A small service in front of a Redis node that
  accepts signed pushes and applies section 4 before writing, for
  public writable nodes.

## 13. Security posture

Content keys are checked on receipt, names and claims are signed and
retractable, so a node can mirror untrusted peers without being
corrupted by them. Public nodes are read-only; writes go through a
gateway or stay inside the owner's trust boundary. The kernel decides
correctness; the protocol guarantees integrity and attribution.

## 14. Today versus this specification

From declbuild's `DeclBuild/Cli/Peer.lean`, `docs/redis-schema.md`,
`docs/attestations.md` and `docs/relative-verification.md`, 2026-10-22.

| item | today (declbuild) | required here | priority |
|---|---|---|---|
| Content-keyed objects, union merge | done | same | — |
| Statement as a first-class object | implicit: a statement exists only as the `stmt` of a stored payload; a node cannot hold a statement without a proof term | Statement object, checkable from its cone alone | **high** |
| Id check on receipt | **not done**: `peer push/pull` copy `cinfo:` and `ids:` without recomputing them | recompute; hold pending until the cone is present | **high** |
| Bindings | `SET bind:{ns}:{name}` on every transferred bundle: last writer wins, a pull can overwrite a local binding; no proof of namespace ownership | namespace id contains the owner key; signed, sequence-numbered bindings | **high** |
| Scheme separation | not checked; signed records name their id scheme, keys do not | manifest declares scheme; no cross-scheme merge | **high** |
| Relative verification | done (`verify-relative`, sessions, daemon); trust set named by CA hashes; signed records | records state `assumes` as ref ids and the base axioms used, so they compose | **high** |
| "Proved" derived across nodes | not computed; CA's folder classifies within one project | section 5, over trusted records | medium |
| Signed verification records | done (Ed25519 over RFC 8785) | same | — |
| Revocation | none | tombstones, key revocation | medium |
| Network queries | one `--registry` URL for lazy fetch; `peer` keeps a named list | section 10 queries over the sources list | medium |
| Difference finding | per-id `EXISTS`; full id list per pull | range-based reconciliation for large selectors | medium (Mathlib scale) |
| Node manifest and sources list | none; `~/.declbuild/peers.json` holds names and URLs | signed manifests; `sources.json` as a list of them | medium |
| Static transport | CA's `registry/` has ids and statuses, no statements or witnesses | statements, optional witnesses, manifest | medium |
| Public write safety | Redis inside a trust boundary | read-only public nodes; gateway for writes | when a public node exists |

## 15. Open questions

- **Pending objects.** How long a node holds an object whose cone is
  incomplete, and whether it asks for the missing pieces or the sender
  must push cones whole.
- **Extension state.** Payloads do not carry simp sets, instances or
  attributes (declbuild's `ext:` and the `.olean` stash). A witness
  checked relative to a statement does not need them; *elaborating* new
  proofs against fetched declarations does. Whether they become
  protocol objects, and under what key, is open.
- **Source fingerprints.** Which context a Lean proof's fingerprint
  should cover (imports, options, toolchain) to be useful for
  reproducing a witness, given it can never be an identity.
- **Reconciliation summary.** Merkle tree over sorted ids versus
  range-based fingerprints.
- **Namespace labels.** `label@key`, or bare keys with labels only in
  manifests.
- **Definitions as assumptions.** Section 5 never assumes a definition
  (its value is meaning, not a claim). declbuild lists "axiomatising
  definitions" as open; under this protocol it would change a
  statement's meaning and is out of scope.

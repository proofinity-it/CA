# Registry protocol, version 1 (draft 2)

> **Status (2026-10-22): draft for discussion, second revision.** This
> document specifies the registry as a protocol between independent
> nodes: which objects exist and which id each is known by, how a
> theorem comes to count as proved across nodes, how a node checks what
> it receives, how nodes merge and find their differences, who may write
> a name, how a claim is retracted, how nodes running different id
> schemes stay apart, and how a node is published and read. The
> canonical published form of a node is one SQLite file; Redis is
> canode's live local store. Section 15 compares the protocol with
> what canode does today; section 16 lists open questions, including
> the one scheme decision that needs a measurement before it can be
> taken. Nothing here is implemented in CA yet.
>
> Changes from draft 1: SQLite file as the published node format and
> transport (§12), replacing one-file-per-object; checkers and mirrors
> distinguished (§4, §11); base-axiom policy (§5); the exact tier's
> practical reach stated honestly, with the core-by-name middle tier as
> an open scheme question (§2, §16); relative verification moved up, as
> the registry's defining feature (§3); a reference implementation and a
> sequencing plan (§14, §17).

## 0. Why a protocol, and why here

There are currently two registries that do not know about each other:

- **CA's registry folder.** A project's `#ca_registry` writes
  `registry/declarations.json`, `statements.json` and `meta.json`
  ([registry-design.md](registry-design.md)), published by `git push`:
  ids, statuses and statements (as units, [payload.md](payload.md)), no
  proofs.
- **canode's Redis network.** Every Redis instance holding
  canode's key schema is a node; `canode publish` and
  `canode peer push/pull` copy keys between nodes. It carries
  payloads, dependency edges, bindings and signed verification records.

Both are views of one thing: a set of content-addressed objects whose
ids are CA's. The rules that make a federation coherent are rules about
those ids, so they belong next to the ids, in CA. canode is one
implementation; Redis is its local store; the published form of a node
is a file any implementation can read.

## 1. Principles

- **The network is the registry; no node is complete.** Nodes hold what
  their owners care about. A node may hold every statement of
  mathematics it has seen and no proofs at all. A question a node cannot
  answer is asked of other nodes (§10); replication is a choice (§10),
  never a requirement.
- **One interchange form, any store behind it.** What crosses an
  ownership boundary is a node file (§12). A **static** node is only
  that file, produced with CA alone (`#ca_registry`, then `ca pack`) and
  published by copying it: nothing to host, no service to run. A
  **live** node keeps its objects in a working store with builds, kernel
  runs and annotations on top (canode's is Redis) and conforms by
  exporting to and importing from the file. Static or live says how a
  node is held, and is independent of checker or mirror (§5), which says
  what it checks on receipt. Running a server is the price of a live
  node's features, never of publishing or reading.
- **The statement is the unit.** Three layers are kept apart:

  | layer | known by | stable under |
  |---|---|---|
  | the **statement** of a theorem | `stmt` | renames and moves of it and of anything it mentions, re-proving, re-elaboration |
  | its **Lean proof** (source) | a fingerprint, a hint only | nothing beyond its exact text and import context |
  | its **proof term** (what an `.olean` holds) | `decl` | renames and moves only: a tactic, Mathlib or the elaborator change it, often with identical source |

  CA names statements. Proofs are **witnesses** of statements: several
  may exist, none is canonical, two witnesses of one statement are never
  in conflict.
- **Nothing downstream depends on a proof**, so a proof can be checked
  *relative to* the statements it uses, treated as axioms, and whether
  a theorem is proved is *derived* from records that compose (§3). This
  is the registry's defining feature.
- **The kernel is the authority, not the network.** The protocol
  guarantees integrity (an object is what its key says) and attribution
  (a claim says who made it). Correctness is decided by a kernel run and
  recorded as a signed claim.
- **A node's state is a join-semilattice.** Merging two nodes is a
  per-key join: commutative, associative, idempotent. Sync is order-free
  and replay-safe.

## 2. Identities, and how far each one reaches

Every statement id hashes the same canonical form, L0 (de Bruijn
indices, universe parameters renamed by position, levels normalised,
`mdata` stripped; hypothesis order and binder info kept). They differ in
what a mentioned constant becomes. The full table of what each id is
stable under is in [ref-hash.md](ref-hash.md#which-id-to-use-where-what-each-is-stable-under);
the rules the protocol takes from it:

- **Everything that composes keys on `ref`** (a theorem's `stmt`, a
  definition's `decl`): dependency edges, the assumptions of a relative
  verification, the derivation of "proved", statement-level annotations.
- **`type_hash` (references by name) is a hint**: discovery and
  cross-toolchain candidates. A coarse match never discharges an
  assumption: two libraries defining `IsSolvable` differently give
  `theorem t : IsSolvable G` one `type_hash`, and a witness from one
  would "discharge" an assumption made in the other with no kernel check
  failing.
- **`decl` of a theorem and `.olean` are caches**, not ids a user cites.

**How far the exact tier reaches.** `stmt` embeds the ids of everything
in the statement's cone, down to Lean's core, so it matches across two
projects only when their cones are byte-identical: in practice, the same
toolchain and the same Mathlib commit. canode measured one minor
toolchain bump (v4.33 → v4.35) at about three quarters of a Mathlib
sample changing `decl`, most of it through core definitions. The
corresponding number for theorems' `stmt` has not been measured and
should be better, since proofs are outside it; it is still expected to
be far from 100 %. Consequently, in a network of projects pinning
different Mathlib months, **the coarse tier will do most cross-project
matching**, and it is blind. The protocol therefore treats a coarse
match as a lead to confirm, offers an explicit equivalence proof
(`A ↔ B`, itself a witness) as the only exact bridge across cones, and
leaves one scheme-level remedy as an open question (§16, *middle tier*).

## 3. Relative verification, and what "proved" means

A **verification record** says: *witness `decl` of statement `stmt` was
kernel-checked by the stock Lean kernel, with the refs in `assumes`
replaced by axioms of their type, and with the base axioms in `axioms`
accepted.* canode's `verify-relative` produces exactly this. What may
be assumed follows `ref`: a theorem by its `stmt` (the kernel never
unfolds a theorem's value), a definition by its `decl` (reduction needs
its value). An assumption is therefore always a ref id, unambiguous
across projects and names.

**Base axioms.** A record lists every axiom the check depended on.
`sorryAx` in that list makes the record **invalid**, not conditional: a
`sorry` is not an assumption, it is the absence of a proof. The default
accepted set is `propext`, `Classical.choice` and `Quot.sound`; any
other axiom (user-declared, or `Lean.ofReduceBool`) is accepted only by
the reader's explicit policy. Readers decide; the record only reports.

**"Proved" is derived, not stored.** Given a set of trusted signers and
an accepted axiom set, a statement S is *proved* when some witness of S
has a trusted, valid record whose every assumption is either a
definition (its `decl` is part of the statement's meaning, not a claim)
or a statement that is itself proved, recursively, with no cycle. S is
*conditional on* {S₁, …} when the recursion bottoms out in statements
with no proved witness; S is *open* when it has no witness with a
trusted record. These are the statuses of CA's registry folder, now
with kernel checks and signatures behind them and computable across
nodes:

- Discharging S₁ anywhere in the network promotes everything verified
  relative to S₁, **without re-checking it**. This is the cross-project
  cascade.
- Two witnesses of S checked relative to different assumptions are both
  kept; S is proved if either chain closes.
- The derivation is a reader's computation over records it trusts. Two
  readers with different trusted signers or axiom policies may disagree,
  by design.

Within one cone (toolchain and Mathlib commit) this composes exactly.
Across cones, a record discharges an assumption only through an
equivalence witness, never through a `type_hash` match.

## 4. Objects

| object | key | content | merge |
|---|---|---|---|
| **Statement** | `stmt` | a statement unit ([`payload.md`](payload.md) §3): the type in L0 form, its level parameters, its references as `ref` ids; hints: `type_hash`, pretty-printed type | identical bytes under identical key |
| **Definition** (any non-theorem) | `decl` (= its `ref`) | a unit (standalone, or the block it belongs to) and one decoration per name ([`payload.md`](payload.md)); kind, `stmt`, dependency set (ref ids) | identical units; a differing unit under one key is a *fault*; decorations union |
| **Witness** | `decl` of a theorem | a unit including the proof term and its decorations; its `stmt`; dependency set; toolchain; hints: source fingerprint, module, name | identical units; decorations union |
| **Witness set** | `stmt` | set of `decl` ids witnessing it | union |
| **Reverse dependencies** | `ref` | set of `decl` ids referencing it | union (derived; may be recomputed) |
| **Verification record** | (`decl`, record digest) | §3: `assumes`, `axioms`, toolchain, policy, signer, signature | union; retracted only by tombstone |
| **Binding** | (namespace, name) | target `decl` or `stmt`, sequence number, owner's signature | highest sequence number wins (§7) |
| **Namespace claim** | namespace | owner key, delegate keys, signature | first valid claim per namespace id |
| **Tombstone** | (target, signer) | retracts a record or revokes a key; signed | union; wins over its target (§8) |
| **Annotation** | `stmt`, `ref` or `decl` | renderings, descriptions, translations; attributed, optionally signed | union |
| **Auxiliary** | (namespace, auxiliary name) | `decl` of a compiler auxiliary; resolvable, never listed | as Binding |
| **Compression dictionary** | content tag | a zstd dictionary that payloads cite | identical bytes |

A **Statement** is deliberately self-contained: with its type bytes and
its name-to-`ref` map, a reader on the same toolchain recomputes `stmt`
(`CA.RefHash.stmtIdOf`) without any other object. That is what lets a
node hold a statement with no proof, and a registry folder be a node.

Non-content metadata travels as **hints**: never part of a key,
droppable, and conflicting hints are all kept, attributed.

## 5. Validity on receipt: checkers and mirrors

Two kinds of node exist, and the protocol expects both.

- A **checker** has a Lean toolchain. It stores an object under a content
  key only after recomputing the key: a Statement's `stmt` from its
  bytes and `ref` map; a Definition's or Witness's `decl`, `stmt` and
  `ref` from the payload (`CA.RefHash.computeIds`), which needs the
  payload's cone, so objects whose cone has not arrived are held
  **pending**, not stored and not served, and senders transfer
  foundations first. Signatures on records, bindings, claims and
  tombstones must verify and the signer must be authorised (§7).
  Unsigned records are accepted as unsigned, or refused, by policy. A
  checker may additionally run the kernel and write a verification
  record; that is a separate act.
- A **mirror** has no toolchain, or chooses not to check. It re-serves
  bytes unchanged and says so in its manifest (§11). A consumer reading
  from a mirror checks for itself. Mirrors are the cheapest nodes and
  the most useful for publication; nothing in the protocol requires a
  server-side check for a node to be worth reading.

A content-id check proves an object is what its key says; it is not a
kernel check and does not make a proof correct.

## 6. Merge

Per-key joins as in §4, plus:

- **Fault.** A unit under a content key whose check (§5) does not give
  that key is a fault. A checker never stores it; it records the peer as
  faulty. A mirror cannot tell and must forward what it has; a consumer
  resolves by checking.
- **Naming variants.** Two different units under one key that both check
  to it are not a fault: they are the same content with different naming
  patterns ([`payload.md`](payload.md) §1, 0.3% of keys in `Init`).
  Both are kept, keyed by (key, variant digest); union.
- **Twins.** Declarations equal up to a consistent renaming share one
  `decl` and one unit; each name has its own decoration, keyed by
  (`decl`, name), not a competitor. (canode's `cinfo-named:` rows
  exist for this because its payload mixes names into the content.)

## 7. Names: namespaces, bindings, authority

Names are the only mutable part of the registry. Contention is made
impossible by making every name belong to exactly one key.

- A **namespace id** is `label@key`, `key` the owner's base58 Ed25519
  public key (`em@2N68kx…`). Two publishers choosing one label get two
  namespaces; short labels are client-side aliases.
- A **Namespace claim** is signed by `key` and may list delegate keys.
  Only the owner can make one, since the id contains the key.
- A **Binding** `(ns, name) ↦ id` carries a sequence number and a
  signature by the owner or a delegate. Merge keeps the highest sequence
  number; ties break on signature bytes. Unbinding is a binding to the
  empty id with a higher number.

A node can therefore accept bindings from anyone and mirror names from
untrusted peers safely.

## 8. Revocation

- A **record tombstone** names a verification record by digest, signed
  by that record's signer; readers treat the record as absent and the
  derivation of §3 changes accordingly.
- A **key revocation** names a key and a time, signed by the key or a
  pre-declared revocation key; that key's later records count as
  unsigned.
- Tombstones are grow-only and never retracted.

## 9. Schemes and toolchains

- Every node manifest declares the scheme version(s) it stores; every
  object is under exactly one scheme; peers **must not** merge across
  schemes. A node may keep several schemes as separate tables or files.
- Toolchains need no special handling: they give different ids for
  anything whose cone changed and identical ids otherwise. `type_hash`
  travels as a hint on Statements and Witnesses for cross-toolchain
  discovery.

## 10. Asking the network, and replicating when wanted

Because no node is complete, the basic operations are queries that a
node answers if it can and otherwise reports as unknown:

| query | answer |
|---|---|
| statement `stmt` | the Statement object |
| witnesses of `stmt` | witness `decl` ids, toolchain, record summaries |
| records for `decl` | verification records (signed, with `assumes`) |
| who depends on `ref` | reverse dependencies the node knows |
| resolve `(ns, name)` | the current binding |
| candidates for `type_hash` | statements with that coarse hash (hints only) |

A reader deriving whether S is proved (§3) issues these against the
nodes in its sources list (§11), in order, caching answers. Lazy fetch
during a check or build is the same mechanism.

**Replication** is union (§6) over a selection:

- **Selectors**: everything; the cone of some roots; a namespace; a
  module prefix; statements only (no witnesses); the witnesses of one
  statement.
- **Difference finding**: ids are sorted keys, so two nodes exchange
  digests of id ranges and recurse only into ranges that differ; small
  selections exchange plain id lists.
- Transfer is foundations first, interruptible and replayable.

## 11. Discovery and the node manifest

- A **node manifest** is a small signed document a node carries and
  serves: its kind (checker or mirror), transports and URLs, schemes,
  toolchains, namespaces held or mirrored, coverage (module prefixes,
  counts, statements only or with witnesses), policy (unsigned records
  accepted or not; read-only or not).
- A **sources list** is a list of manifests, or URLs serving them, with
  the expected signing key for each. CA's `sources.json` is this list
  without the manifests yet: name, kind (folder or node), location, and
  an optional key that is parsed but not checked. A reader merges the
  lists it trusts.

## 12. Transports and store formats

The protocol is the objects and rules above; a store format is how a
node keeps them, a transport is how bytes move. Three are defined.

**SQLite file — the canonical published node.** Normative for
interchange: two implementations exchange nodes in this form and no
other, and a static node (§1) is this file and nothing else. A node is
one SQLite file, one table per object type, content ids as primary
keys, plus a `meta` table holding the manifest:

```
meta        (key, value)                       -- manifest: kind, scheme, toolchains, policy, signer
refs        (ix PK, ref)                       -- payload.md §6: the file's ref table
names       (ix PK, name, display)             -- and its name table
units       (id PK, key, variant, form, bytes) -- payload.md §3, statements included (form 0)
members     (decl, name, unit, member)         -- each bound name → its unit
decorations (decl, name, bytes)                -- names, binders, hints (payload.md §4)
declarations(decl PK, kind, stmt, ref)         -- definitions and witnesses
witnesses   (stmt, decl, PK(stmt, decl))
entries     (name PK, stmt, status, type_hash) -- registry entries; statement unit in units
deps        (decl, ref, PK(decl, ref))
records     (decl, digest PK, json, signer, valid)
bindings    (ns, name, seq, target, sig, PK(ns, name, seq))
namespaces  (ns PK, owner_key, delegates, sig)
tombstones  (target PK, kind, signer, sig, json)
annotations (id, kind, digest PK, json, signer)
dicts       (tag PK, bytes)
```

`ca pack` writes, and `ca check` checks, every table but `annotations`
and `dicts` ([payload.md](payload.md) §6 has the exact columns of the
first five): `deps` (each declaration's references outside its unit, by
ref id, checked against the unit's slots), `records` (written by
`ca verify`: the §3 JSON, its SHA-256 digest, the signer's key and an
Ed25519 signature over the digest, `valid`), `namespaces` and `bindings`
(written by `ca pack --sign`: the claim of `label@key` and one signed,
sequence-numbered binding per registry entry, name ↦ `ref`). Signatures
are Ed25519 in pure Lean (`CA.Ed25519`, RFC 8032) and in Python's
standard library (`tools/ed25519_ref.py`), so a build and a stdlib-only
checker both verify them. A statement is a unit of form 0 keyed by its
`stmt`, so there is no separate statements table; a pretty-printed type
and `type_hash` are hints in `entries`.

Why this is the published form:

- *Merge is SQL.* `ATTACH` the other node, `INSERT OR IGNORE` per
  table; bindings with a `WHERE seq >`. The semilattice is literal.
- *Reconciliation is SQL.* Primary keys are sorted; a range digest is a
  `GROUP BY substr(id, 1, k)`.
- *Hosting is a file.* Any static host serves it; a reader can query it
  over HTTP range requests without downloading it whole. Publication is
  copying a file; a mirror is a copy.
- *Everyone can read it*: Lean through
  [`leanprover/leansqlite`](https://reservoir.lean-lang.org/@leanprover/leansqlite)
  (which bundles the SQLite amalgamation, so no system library), Python
  through its standard library, any tool, any agent, no Lean installed.
- *A node can hold everything.* Disk-resident; coverage is a choice.

The file is produced by a tool (`ca pack`, or canode) from a registry
folder plus the environment, or exported from a live store; it is not
committed to a source tree (a binary in git has no diffs) but attached
to releases or served from a pages branch. `declarations.json` remains
the human-readable index next to the source.

**Redis — canode's live local store.** A Redis instance holding
canode's key schema (`cinfo:`, `ids:`, `deps:`, `stmt:`, `rdeps:`,
`verifications:`, `bind:`, `aux:`, `meta:zstd-dict:`) is the hot path of
a build: RAM-resident, shared by the daemon and the CLI. Node-to-node
copy between Redis instances (`peer push/pull`) remains as it is, inside
a trust boundary, since Redis has no per-key authorisation. Exporting a
Redis node to the SQLite form and importing one are the bridge between
the two; canode's project state, daemon queues and `graph:*`
compactions are local and never exported. Redis is one live store, not
part of the protocol: another implementation may keep its live node in
anything, provided it exports and imports the file. Likewise the `ca`
CLI's Redis keys (`ca:decl:*`, written by `ca fetch` / `ca address`)
are a local index for its own lookups, not a node.

**Gateway — if a public writable node is wanted.** A small service in
front of a store that accepts signed pushes and applies §5 before
writing. Not needed while publication is file copy.

## 13. Security posture

Content keys are checked by checkers and by consumers; names and claims
are signed and retractable; a mirror can serve untrusted content without
being able to corrupt a consumer that checks. Public nodes are files or
read-only replicas; writes happen inside the owner's trust boundary or
through a gateway. The kernel decides correctness; the protocol
guarantees integrity and attribution.

## 14. Reference implementation

CA already has one for the ids: `tools/refhash_ref.py`, written from
`spec.md` alone, reproduces its test vectors. The protocol gets the
same treatment: `tools/registry_ref.py`, Python standard library only,
operating on the SQLite form. **Built so far** (2026-10-23): validity on
receipt for content, i.e. every unit's ids recomputed from its bytes
([payload.md](payload.md) §5) and every member, declaration, witness and
entry row checked against them; it agrees with `ca check` on every unit
of an `Init` node file and reproduces payload.md §9's vectors.
**Also built** (2026-10-23): records (digest, declaration row, stmt
field), Ed25519 signatures on records, namespace claims and bindings
(`tools/ed25519_ref.py`), binding targets present in the file, and the
§3 derivation of `proved` / `conditional` over the valid records of one
file (a statement is proved when some witness has a valid record whose
every assumption is a definition or a proved statement, no cycle).
**Also built:** merge (`CA.Node.merge`, checked by both implementations
on the result) and range digests with difference finding (`CA.Node.diff`).
**Still to do:** the derivation across several files and over trusted
signers only, binding resolution by `(ns, name)`. Two
implementations that agree on a file, the Python one and the Lean one,
are the conformance test; `cli/tests/node-test.sh` runs both on every
file it writes, signed and unsigned, intact and tampered.

## 15. Today versus this specification

From canode's `Canode/Cli/Peer.lean`, `docs/redis-schema.md`,
`docs/attestations.md`, `docs/relative-verification.md`, 2026-10-23.
Where CA itself now provides the piece (v0.3.0), the row says so.

| item | today (canode) | required here | priority |
|---|---|---|---|
| Content-keyed objects, union merge | done | same | — |
| Relative verification | done; trust set as CA hashes; signed records; `sorryAx` fails the check and gets no record, `attest` skips a `sorry` declaration (2026-10-23). CA alone: `ca verify` rebuilds a node file's declarations, the kernel judges, records state `assumes` (ref ids of statements assumed from their statement units) and `axioms`; `sorryAx` makes the record invalid | records state `assumes` as ref ids and `axioms` | **high** |
| Statement as a first-class object | implicit only: a statement exists as the `stmt` of a stored payload. CA has the object: a statement unit ([payload.md](payload.md) §3), in every `statements.json` and node file | Statement with type bytes and `ref` map, holdable without a proof | **high** |
| Published node format | **done** (2026-10-23): `canode node export` writes the store's modules as a node file from Redis alone, ids recomputed and compared; `node import` checks a file (`CA.Node.checkNode`) and rebuilds every name. CA writes and checks the file too (`ca pack`, `ca check`, `tools/registry_ref.py`) | SQLite file export / import | — |
| Id check on receipt | **not done** in `peer push/pull`. For node files it is `ca check` / `CA.Node.checkNode` | checkers recompute; mirrors declare | **high** |
| Bindings | plain `SET`, last writer wins; no ownership proof (acknowledged open). In node files: `ca pack --sign` writes a claim of `label@key` and signed, sequence-numbered bindings; `ca check` and `registry_ref.py` verify them | namespace id contains the owner key; signed, sequence-numbered | **high** |
| Scheme separation | **done** (2026-10-23): the store declares `meta:id_scheme`; `peer`, `fetch` and `use` refuse a mismatch, or a node with content and no declared scheme | manifest declares; no cross-scheme merge | — |
| "Proved" derived across nodes | not computed in canode; `registry_ref.py` derives it over one node file's valid records | §3 over trusted records, across nodes | medium |
| Revocation | none | tombstones, key revocation | medium |
| Network queries | one `--registry` URL for lazy fetch; `peer` list of nodes | §10 over the sources list | medium |
| Difference finding | per-id `EXISTS`; full id list per pull | range digests over sorted keys | medium |
| Node manifest and sources list | none; `~/.canode/peers.json` | signed manifests; `sources.json` | medium |
| Twins across nodes | `cinfo-named:` rows not carried by `peer` (acknowledged). In a node file the format solves it: one unit, one decoration per name ([payload.md](payload.md) §1) | carried as named variants | low |
| Public write safety | Redis inside a trust boundary | files and read-only replicas; gateway if ever needed | when needed |

## 16. Open questions

- **Middle tier (a scheme decision).** A statement id whose references
  into the toolchain's *core* resolve by name and everything above core
  by id would survive most toolchain bumps while staying exact for
  project and library definitions, at the price of deliberate blindness
  to core redefinitions, which ship reviewed with the toolchain. The
  spec has the mechanism (by-name encoding of a reference). Whether to
  add it depends on a measurement nobody has made: of the churn across
  one toolchain bump, how much enters through core. If most of it, the
  middle tier removes most of the need for equivalence proofs; if not,
  it buys little. Measure `stmt` survival for theorems with and without
  the cut before deciding. (The other measurement `spec.md` §13 asked
  for is done: full and statement mode agree on every `stmt` and `ref` of
  `Init`, [payload.md](payload.md) §7, so a node may keep statements
  without proofs at no cost in identity.)
- **Pending objects.** How long a checker holds an object whose cone is
  incomplete, and whether it requests the missing pieces or the sender
  must transfer cones whole.
- **Extension state.** Payloads do not carry simp sets, instances or
  attributes (canode's `ext:` and the `.olean` stash). A witness
  checked relative to a statement does not need them; *elaborating* new
  proofs against fetched declarations does. Whether they become
  protocol objects, and under what key, is open.
- **Source fingerprints.** What context a Lean proof's fingerprint
  should cover (imports, options, toolchain) to help reproduce a
  witness, given it can never be an identity.
- **Range digests.** Prefix buckets versus a Merkle tree over sorted
  ids; the SQLite form makes either a query.
- **Namespace labels.** `label@key`, or bare keys with labels only in
  manifests.
- **Definitions as assumptions.** §3 never assumes a definition (its
  value is meaning, not a claim). canode lists "axiomatising
  definitions" as open; under this protocol it would change a
  statement's meaning and is out of scope.

## 17. Sequencing

In CA, in this order: Statement objects in the registry folder (type
bytes and `ref` map per entry, so a folder is a node readable on the
same toolchain; **done**, `statements.json`); `ca pack` (**done**, with
`ca check`) producing the SQLite form from a folder and
an environment; `tools/registry_ref.py` (**content checks done**, §14);
`sources.json` (**done**, with `ca lookup`, `#ca_lookup` and `resolve%`);
the two
measurements (`stmt` survival across a toolchain bump, with and without
the core cut; the full-mode versus statement-mode `stmt` mismatch rate
from `spec.md` §13).

In CA, done (2026-10-23): merge of node files (`ca merge`, `CA.Node.merge`,
units remapped onto one table), range digests and difference finding
(`ca digest`, `ca diff`). Next: the derivation of "proved" across files
and over trusted signers only ([plan.md](plan.md) item 3 leftovers).

In canode: records with `assumes` as ref ids and `axioms`; SQLite
export and import of a node (through `ca-nodefile`); id check on receipt
in `peer`; signed bindings; statements stored without proofs.

Not before the above: more Redis-to-Redis sync machinery (no second
project publishes a node yet), and the equivalence-proof layer (the
middle-tier measurement may remove most of its need).

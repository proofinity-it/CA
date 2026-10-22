# `CA.RefHash` — content identity per declaration

`CA.RefHash` is the identity scheme CA recommends for declarations: the
key of a declaration store (declbuild uses it so) and, once emitted, the
exact tier of the registry key next to the coarse name-based hash. It
exists because the name-based L0 type hash

1. keeps constant **names** inside the type, so `theorem t : IsSolvable G`
   hashes the same in two libraries whose `IsSolvable` differ — the
   hole a decentralized registry cannot have; and
2. hashes the **type only**, so every `inductive Foo : Type` and every
   definition of a given type collide (measured on a Mathlib store:
   270 inductives under the id of `Type`).

The L0 hash remains the right notion of a *statement* — once its
references are ids instead of names — which is exactly `stmt` below.

The byte-level specification, with test vectors, is [spec.md](spec.md).
This page explains the design.

## The three ids

For a constant `c`, foundations first over the reference DAG:

```
ref(c)  = stmt(c)   if c is a theorem      -- proof irrelevance: no dependent
                                           -- can observe the proof
        = decl(c)   otherwise              -- a definition IS its value

stmt(c) = H( STMT ‖ v ‖ #levelParams ‖ ⟦type c⟧ )
decl(c) = H( DECL ‖ v ‖ kind ‖ flags ‖ stmt(c) ‖ ⟦value c⟧? ‖ structural fields )
```

`v` is the encoding-scheme version byte (`CA.schemeVersion`, currently 1;
see *Scheme versions* below). `⟦e⟧` is the id of the L0-canonical
expression `e` (`mdata` stripped; universe levels normalised with
`Level.normalize` *after* renaming, so `max u v`/`max v u` and
`max u u`/`u` agree while the normal form never sees the original
parameter names; `Nat` literals encoded as length-prefixed big-endian
bytes at full precision;
universe parameters renamed **positionally** from the declaration's
`levelParams` binder list, `levelParams[i] ↦ u_i` — renaming the
binders is erased, *reordering* them is not, because use sites
instantiate levels positionally: `def q1.{u,v} : F u v` and
`def q2.{u,v} : F v u` are different declarations and get different
ids, where per-expression first-occurrence renaming made them collide),
computed **Merkle-style**: a node's id
is `H(tag ‖ scalars ‖ ids of children)`, and a `.const r` node embeds
`ref(r)`. Shallow subterms (`approxDepth ≤ 6`) are hashed flat in one
SHA-256; deeper ones from their children with a memo on structurally
equal subterms, so `decide`-style proofs whose *tree* is huge but whose
DAG is small stay linear. `.proj S i e` embeds `ref(S)`. Binder names
never enter; binder info does. The per-subterm ids are well defined
because the whole term is closed: an open subterm's id depends on its
de Bruijn indices and so on its position under enclosing binders, which
makes it a sound memo key (same structure, same id — the shared memo
relies on exactly this) but not an α-invariant address of the fragment.
Only the root, a closed term, is an address. `ReducibilityHints` do not enter (they
steer the elaborator, not the theory); `DefinitionSafety`, `isUnsafe`,
inductive arity/flags, constructor index/arity, recursor arity/rules/`k`
do.

Kind-by-kind, what is proof-irrelevant to dependents: only `theorem`
(`isProofIrrelevant`). `axiom` has no value, so `decl(axiom) =
H(kind ‖ stmt)` and two axioms of one statement coincide — as they should:
nothing inside the type theory can tell them apart. `opaque` is kept
value-inclusive, deliberately conservative for a build system (a
changed body changes compiled code even though no type-checker can
tell); relax later if wanted.

## Which id to use where: what each is stable under

L0 is a canonical *form*, not an id: de Bruijn indices (α-equivalence),
universe parameters renamed by position, levels normalised, `mdata`
stripped; hypothesis order and binder info are kept. Every id below
that hashes a statement hashes its L0 form; they differ in what a
mentioned constant becomes.

| id | what it hashes | stable under | changes when | blind to |
|---|---|---|---|---|
| `type_hash` | L0 statement, references by **name** | renaming or moving the declaration, re-proving, α-renaming, universe renaming, toolchain releases | statement shape, hypothesis order or binder info change; a mentioned name is renamed | redefinition behind an unchanged name: false merges |
| `stmt` | L0 statement, references by **id** | the above, plus renaming or moving anything it mentions | shape, order or binder info; any type or definition value in its cone (including Lean's core across releases); scheme bump | nothing in its cone; definitionally equal reformulations stay distinct |
| `ref`, theorem | `= stmt` | as `stmt`; its own proof never matters | as `stmt` | — |
| `ref`, definition | `= decl` | renaming, moving | its value, or anything in the value's cone | — |
| `decl`, theorem | statement, kind, proof term | renaming, moving | the proof term: a tactic, Mathlib, the elaborator, often with identical source | — |
| source proof fingerprint | proof text plus import context | nothing beyond itself | any edit, or any change in context | what it elaborates to |
| `.olean` | a whole module, compiled | nothing | any declaration in the module, or the toolchain | — |
| binding `(namespace, name)` | a pointer, not content | until its owner rebinds it | the owner's decision | content, by design |
| verification record | a signed claim | forever: grow-only, retracted only by a tombstone | never; new records are added | whether the kernel actually ran: it attests who said so |

Rules that follow from the "stable under" column:

- Anything that must survive rewriting a proof keys on `ref` — for a
  theorem, its `stmt`. Citations, dependency edges, assumptions of a
  relative verification, statement-level annotations.
- Anything that must survive a toolchain release can only use
  `type_hash`, and only as a hint: a coarse match is a candidate, to be
  confirmed in one shared environment or by an equivalence proof, never
  a discharge of an assumption. Names are exact only inside one fixed
  environment, so (`type_hash`, environment fingerprint) is exact but
  invalidated by any change anywhere in that environment.
- `decl` of a theorem and `.olean` are caches and verification keys, not
  identities a user should cite.

## Blocks

Mutual definitions and inductive families are cyclic. Each strongly
connected component of the reference graph (Tarjan, iterative) is one
**block**:

* members are put in a canonical order: primary key the member's
  encoding with intra-block references made anonymous, tie-break by
  source position (`all` index / constructor index) — the tie-break only
  matters for members that are structurally identical up to renaming;
* intra-block references are encoded as `BLOCKREF ‖ index`;
* `block = H(BLOCK ‖ v ‖ n ‖ member₀ ‖ … ‖ memberₙ₋₁)` and
  `decl(mᵢ) = H(MEMBER ‖ v ‖ block ‖ i)`;
* each member's `stmt` is then computed with the sibling `decl`s as
  ordinary references.

An inductive's constructors are in its block (the type lists them, they
reference the type); its recursor is a downstream node referencing the
block. Self-recursive constants (`foo._unsafe_rec`) are one-member
blocks. Universe-polymorphic blocks are covered by the per-member
level-param count and the canonical universe naming.

## Scheme versions

Every top-level preimage carries `CA.schemeVersion` right after its
domain tag, so ids computed under different encodings can never
coincide by accident, and `meta.json` records the same number as
`ca_scheme_version`. A bump means: *ids changed; recompute*.

| scheme | release | change |
|---|---|---|
| 0 | pre-release development | no version byte; `Nat` literals truncated to 64 bits (`2^64` collided with `0`); universe levels hashed syntactically (`max u v` ≠ `max v u`) |
| 1 | v0.1.0 and later | version byte; literals as length-prefixed big-endian bytes; `Level.normalize` after positional renaming |

`lake exe refhash-test` pins **golden ids** for declarations that
reference nothing outside their own block (`T`, `T.a`, `T.rec`, `idT`),
which therefore depend only on the scheme and not on the toolchain. An
unintended encoding change fails those checks; an intended one updates
them together with the version.

## Unresolved references

`computeIds decls base` resolves references to constants outside
`decls` through `base : RefTable` (name → ref). Anything in neither is
hashed **by name** and reported in `DeclIds.unresolved`; such ids are
*not* exact and never enter the shared memo — subterm memo entries
carry a dirty flag so that a cached fallback-bearing subterm still
poisons every enclosing term (and `unresolved` stays complete even
when a term is served from the cross-declaration memo). To get exact ids for a
subset (e.g. one library on top of another), compute the base first —
`computeIds` over `Init` yields 0 unresolved.

## API

```lean
CA.RefHash.computeIds : Array (Name × ConstantInfo) → RefTable → (hasher : Hasher := pureHasher)
                        → (withProofs : Bool := true) → IO (Array DeclIds × RefTable)
CA.RefHash.idsOf      : Name → ConstantInfo → RefTable → (hasher := pureHasher) → IO DeclIds
CA.RefHash.stmtIdOf   : List Name → Expr → RefTable → (hasher := pureHasher) → IO (ByteArray × Array Name)
CA.RefHash.refsOf     : ConstantInfo → (withProofs : Bool := true) → NameSet  -- exact reference set (incl. structural)
CA.RefHash.sccs       : Array Name → (Name → Array Name) → Array (Array Name)
CA.RefHash.toB58      : ByteArray → String
```

`DeclIds = { name, stmt, decl, ref, block? : (blockId × index), unresolved }`.

`withProofs := false` leaves theorem proofs out: not hashed, not followed
as references. `stmt` and `ref` of every declaration are unchanged (a
theorem's `ref` *is* its `stmt`); a theorem's `decl` becomes the
statement-only `H(DECL ‖ v ‖ kind ‖ stmt)`. This is the mode for the ids
a registry or a dependent needs, where no proof term is observable, and
it makes the required cone of an environment a small fraction of it —
`∀ n : Nat, n + 0 = n` needs 30 constants of `Init`, five assorted
statements about `Nat.gcd`, `Array.qsort` and `String` about 550.

`stmtIdOf levelParams e table` is the statement id of a bare expression
`e`, as if it were the type of a theorem: `H(STMT ‖ v ‖ #levelParams ‖
⟦e⟧)`. The registry uses it for an `@[open_point]` `def P : Prop := S`,
whose statement is `S`: a theorem `: S` gets exactly this `stmt`.

## Properties (checked by `lake exe refhash-test`, over `Init` as base)

* α-renamed declarations get equal ids (names never enter);
* theorems: same statement ⇒ same `stmt`/`ref`; different proof ⇒
  different `decl`;
* definitions: same type ⇒ same `stmt`; different value ⇒ different
  `decl`/`ref`, and statements *about* them differ accordingly;
* mutual / inductive blocks share a block id with distinct indices;
* universe binder *order* is part of the identity (positional
  instantiation), binder *names* are not;
* ordinary (non-mutual, non-self-referential) declarations are
  standalone — no block id;
* `unresolved` is complete even for subterms served from the shared
  memo;
* `Nat` literals at full precision (`2^64` ≠ `0`); definitionally equal
  universe levels give equal ids;
* `stmtIdOf` of a `def P : Prop := S`'s value equals the `stmt` of a
  theorem `: S`; `withProofs := false` preserves every `stmt` and `ref`
  and changes only theorems' `decl`;
* golden ids for toolchain-independent declarations match the pinned
  values for the current scheme version;
* deterministic, input-order independent; 0 unresolved on `Init`.

Throughput, single-threaded on `Init` (66k declarations): ~4.5k
declarations/s with the CLI's OpenSSL hasher (~14 s), ~2k/s with the
library's pure-Lean default (~34 s). SCC levels are independent, so this
parallelises when needed.

## What a store does with the three ids

`stmt` keys statements: registry matching, "has this been proved?",
statement-level annotations (renderings, descriptions). `decl` keys
stored declarations (constant info, kind, module, dependencies,
verification records). `ref` is what dependency edges and cone walks
use, so that re-proving a theorem invalidates nothing downstream while
changing a definition's value invalidates everything that could unfold
it. This is how declbuild (not yet public) uses them; the registry emits
`stmt` and `ref` next to the coarse name-based `type_hash`
([registry-design.md](registry-design.md), *The two-tier key*).

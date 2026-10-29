# `CA.RefHash` — content identity per declaration

`CA.RefHash` is the identity scheme CA recommends for declarations: the
key of a declaration store (canode uses it so) and, once emitted, the
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

## The name-based hash: cost, and the planned rework

*Measured 2026-10-29; the rework is a plan, not yet implemented.*

`type_hash` (`CA.ExprHash`, the CLI's `ca address`) and `stmt` hash the
same L0 form, but not the same way. `stmt` is Merkle-style with a memo
on structurally equal subterms (above), so its cost is the size of the
statement's **DAG**. `type_hash` serialises the whole statement into one
byte array (`serializeExpr`, a pre-order walk with no memo) and hashes
that, so its cost, in time and memory, is the size of the statement's
**tree**. Elaborated statements are DAGs whose trees can be
exponentially larger: instance arguments, implicit types and coercions
repeat the same subterm at every level.

On the Lean Pool corpus (318 projects, toolchain `v4.35.0-rc3`), `ca
pack` (`stmt`) took 10 to 40 s per project, these four included; `ca address` (`type_hash`)
blew up on four of them (ConnesRigidity, JacobianDiffgeo, LiebThirring,
Malliavin), past an 8 GB cap each. ConnesRigidity reached 37.7 GB for
1,899 declarations before the kernel killed it: at least twelve of its
statements have about 1,000 distinct subterms and more than 10⁸ nodes as
trees. Mathlib itself passes, but `ca address` on its own 372k
declarations (`v4.35.0`) peaks at 18.5 GB against 10.3 GB for `ca pack`
on all of Mathlib. L1 has the same weakness, worse: `deepNormalize`
walks the tree with no memo, and opens and re-closes every binder
(`withLocalDecl`, `mkForallFVars`), so the body under each binder is
traversed again.

This is not a defect of content addressing but of one implementation
of it, and the literature names both halves. Maziarz, Ellis, Lawrence,
Fitzgibbon and Peyton Jones, *Hashing Modulo Alpha-Equivalence* (PLDI
2021), solve a harder problem than ours (α-equivalence classes of
*every* subexpression, open ones included, for CSE) and make three
remarks that apply here:

- **De Bruijn is right for a closed root, wrong for open fragments**
  (their §2.4): de Bruijn hashes of open subterms give false negatives
  and false positives, while being "great for structure sharing". CA
  already draws that line: subterm ids are memo keys, only the closed
  root is an address (above).
- **Merkle hashing with a memo is the standard answer for syntactic
  identity** (their §2.3: hash a node from its constructor and its
  children's hashes, "we simply memoise the node constructor
  functions"). On a closed de Bruijn term that is exactly identity
  modulo α, in time linear in the DAG. `stmt` does this; `type_hash`
  does not.
- **Locally nameless costs a re-hash under each binder** (their §2.5),
  the pattern L1 pays today by opening every binder.

Their weak (XOR) combiner is needed only for free-variable maps, which
a closed root does not have; with SHA-256 at every node and an
injective encoding (domain tag, kind tag, fixed-size child digests,
length-prefixed names), collision resistance reduces to SHA-256's, as
for any hash tree. Their correctness argument is CA's too, in two steps:
a canonical form that loses nothing but what the equivalence erases
(their e-summary, our L0 expression), then an ordinary hash, the only
step that can collide.

**The rework.**

1. **One engine, two leaf policies.** `type_hash` becomes the Merkle
   hash of the same L0 form with the same flat/Merkle split and memo as
   `⟦·⟧`, a `.const` leaf encoding its **name** (length-prefixed
   components) instead of its `ref`, under its own domain tag so the
   two can never coincide. Cost becomes the DAG's, as for `stmt`.
2. **One pass.** `ca pack` emits `type_hash` for every declaration it
   packs, not only for `@[publish]` entries, from the same traversal
   that computes `stmt`: no second environment load and no separate
   `ca address` run, which is the one that needed 18.5 GB on Mathlib.
3. **L1 on the same engine.** `deepNormalize` gets a memo on
   structurally equal subterms; the L1 id is then the Merkle hash of the
   normalised form.
4. **A version for the name-based hash.** Its values change, so
   `meta.json` records a `type_hash` scheme next to
   `ca_scheme_version`, and the two are never compared across schemes.
   `stmt`, `decl` and `ref` do not change: scheme 1 stands.

What it buys: every id CA computes costs the size of the DAG, so no
statement can take a machine down; `type_hash`, the only id that
crosses toolchain releases, becomes cheap enough to emit everywhere,
which is what comparing corpora at different toolchains needs.

What it does not change: what each id identifies. Argument order and
binder info stay part of every id (the table above). A coarser layer,
up to the order of independent hypotheses, is the next question; the
rule for it is the two-step one above — a canonical order (a
topological sort of the binder telescope with position-free tie-breaks)
and a bridge the kernel checks (the permutation, as a term each way),
never a lossy hash taken on trust. Maziarz et al. name this level
(their "graph equivalence", reordering independent `let`s) and leave it
out of scope; for binder telescopes it needs canonical ordering, not
their machinery.

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
it. This is how canode (not yet public) uses them; the registry emits
`stmt` and `ref` next to the coarse name-based `type_hash`
([registry-design.md](registry-design.md), *The two-tier key*).

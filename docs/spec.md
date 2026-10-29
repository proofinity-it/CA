# CA content identity — specification, scheme 1

Status: **normative** for encoding scheme 1 (every public CA release, v0.1.0 and later),
and, in §15, for scheme 2 of the name-based `type_hash` (not yet emitted by any release).
Conformance is checked by the vectors in §12. An independent
implementation written from this document alone,
[`tools/refhash_ref.py`](../tools/refhash_ref.py), reproduces all of
them. [`ref-hash.md`](ref-hash.md) explains the design and its
rationale; this document says only what the bytes are. How a
declaration is *stored* so that these ids can be recomputed from it is
[`payload.md`](payload.md) (draft); it does not affect any id.

The key words MUST, MUST NOT, SHOULD and MAY are used as in RFC 2119.

## 1. Scope

The scheme assigns three 32-byte identifiers to every constant of a Lean 4
kernel environment:

| id | identifies | used as |
|---|---|---|
| `stmt` | the statement: the type, with its universe arity | key of "what is claimed" |
| `decl` | the whole declaration: kind, statement, value, structural fields | key of a stored declaration |
| `ref` | what a dependent may observe: `stmt` for a theorem, `decl` otherwise | what other ids embed when they mention the constant |

The ids depend on the **content** of a declaration and, through `ref`, on
the content of everything it references. They never depend on names, on
modules or files, on binder names, or on the order in which declarations
were elaborated. They do depend on the kernel terms. Two elaborations of
the same source that produce different terms get different ids.

The scheme does not define ids for open terms. The root of a closed term
is an address. Subterm ids (§7) are intermediate values, sound for
memoisation, not addresses (`worked-example.md` §4 explains why).

## 2. Notation

- `‖` is byte concatenation; `H(x)` is SHA-256 (FIPS 180-4) of `x`, 32 bytes.
- `v` is the scheme version byte, `0x01` for this document.
- Integer literals such as `0xA1` denote single bytes.
- A *name* is a Lean `Name`. Only §9's reference resolution and §10's
  fallback look at names; no exact id contains one.

## 3. Primitive encodings

| notation | encoding |
|---|---|
| `u8(x)` | one byte |
| `u64(n)` | 8 bytes, little-endian, `n mod 2^64` |
| `bytes(b)` | `u64(len b) ‖ b` |
| `str(s)` | `bytes(UTF-8 of s)` |
| `bignat(n)` | `bytes(minimal big-endian bytes of n)`; `n = 0` is the empty byte string |
| `name(n)` | `str(n.toString)`, Lean's dotted rendering (escaping included) |
| `xname(n)` | `u64(k) ‖ c₁ ‖ … ‖ cₖ` over the `k` components, each `0x00 ‖ str(s)` (string) or `0x01 ‖ u64(i)` (number): injective, unlike `name` (§15 only) |

`u64` is used for counts, indices and de Bruijn indices, which are far
below `2^64`. Natural-number **literals** MUST use `bignat`, at full
precision.

**Rendering.** Ids are displayed in base58btc: the Bitcoin alphabet
`123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz`, the 32
bytes read as one big-endian integer, each leading zero byte rendered as
`1`, and no checksum. Rendering is not part of the identity. Hex is
equally valid.

## 4. Input

The input is a set of constants, each a Lean 4 kernel `ConstantInfo`.
The fields read are:

| kind | fields read |
|---|---|
| all | `levelParams` (the universe binder list), `type` |
| `axiom` | `isUnsafe` |
| `defn` | `value`, `safety` (`safe`/`unsafe`/`partial`), `all` |
| `thm` | `value`, `all` |
| `opaque` | `value`, `isUnsafe`, `all` |
| `quot` | `kind` (`type`/`ctor`/`lift`/`ind`) |
| `induct` | `numParams`, `numIndices`, `numNested`, `isRec`, `isUnsafe`, `isReflexive`, `ctors`, `all` |
| `ctor` | `induct`, `cidx`, `numParams`, `numFields`, `isUnsafe` |
| `rec` | `numParams`, `numIndices`, `numMotives`, `numMinors`, `k`, `isUnsafe`, `rules` (each `ctor`, `nfields`, `rhs`), `all` |

Fields not listed MUST NOT affect the ids. That includes the
declaration's own name, `ReducibilityHints`, binder names, the `nonDep`
flag of `let`, and `mdata` contents.

`Expr` and `Level` are Lean 4's kernel types. `fvar`, `mvar` and level
`mvar` do not occur in kernel declarations. Their encodings are listed
for totality only (§7).

## 5. Universe levels

### 5.1 Encoding

```
lvl(zero)       = 0x10
lvl(succ l)     = 0x11 ‖ lvl(l)
lvl(max a b)    = 0x12 ‖ lvl(a) ‖ lvl(b)
lvl(imax a b)   = 0x13 ‖ lvl(a) ‖ lvl(b)
lvl(param p)    = 0x14 ‖ name(p)
lvl(mvar m)     = 0x15 ‖ name(m)
```

After canonicalisation (§6) the only parameter names that occur are
`u_0`, `u_1`, ….

### 5.2 Normal form

Every level is replaced by its normal form `norm(l)` before encoding.
`norm` is Lean 4's `Level.normalize` (`src/Lean/Level.lean`; this
document is checked against v4.35.0), restated here:

1. If `l` is `zero`, a `param`, or `succ` applied to one of these, `norm(l) = l`.
2. Otherwise write `l = succᵏ(u)`, where `u` is `max` or `imax`.
3. `u = max a b`: flatten nested `max` on both sides into a list,
   normalising each non-`max` argument and flattening again if the result
   is a `max`. Sort the list by `normLt`. Let `f` be the index of the
   first element whose base (the level under its `succ`s) is not `zero`.
   If `f > 0` and some element at index `≥ f` has an offset at least the
   offset of element `f-1`, start at `i = f`, otherwise at `i = f-1`. From
   index `i` on, merge consecutive elements with the same base, keeping
   the later one. Fold left into `max(…, succ^(k+offset)(base))`, with
   `zero` as the empty accumulator.
4. `u = imax a b`: if `b` is never zero (`succ _`; `max` with a
   never-zero side; `imax _ c` with `c` never zero), the result is
   `succᵏ(norm(max a b))`. Otherwise normalise `a` and `b`, then: `b = zero`
   ↦ `zero`; `a = zero` or `a = succ zero` ↦ `b`; `a = b` ↦ `a`; else
   `imax a b`. Apply `succᵏ` to the result.

`normLt(l₁, l₂)` strips `succ`s into offsets `k₁`, `k₂`, then compares as
follows:
- equal bases: compare the offsets;
- both `max`, or both `imax`: compare the first differing argument
  recursively;
- both `param`: compare by `Name.lt`, which orders the components of a
  dotted name lexicographically, strings by code point, so `u_10 < u_2`;
- otherwise: order by constructor, `zero < param < mvar < succ < max < imax`.

The point is that definitionally equal levels hash alike. `max u v` and
`max v u` agree, `max u u` and `u` agree, and `imax u (v+1)` and
`max u (v+1)` agree. `norm` is not a complete decision procedure for
level equality, and the identity is defined by `norm` as stated, not by
level equality (§13).

## 6. Canonicalisation

For a declaration with universe binder list `ps = [p₀, …, pₙ₋₁]`, every
expression read from it (type, value, recursor rule right-hand sides) is
canonicalised with respect to `ps`:

1. **Positional universe renaming.** `pᵢ ↦ u_i`. A parameter occurring in
   the expression but not in `ps` is appended in first-occurrence order
   (pre-order, left to right). This is ill-formed input, accepted for
   totality.
2. **Level normal form.** Every level of every `sort` and `const` node is
   replaced by `norm` of the renamed level (§5.2). This applies also when
   no parameter occurs, so `max 1 1` becomes `1`.
3. **`mdata` removal.** Every `mdata _ e` is replaced by `e`.

Renaming the binders leaves ids unchanged. *Reordering* them changes the
ids, because use sites instantiate levels by position.

## 7. Expression ids

`⟦e⟧_R` is the id of the canonical expression `e` under a resolver `R`,
which maps each referenced name to a *reference encoding*:

```
renc(id r)        = 0x31 ‖ r                  -- r: the 32-byte ref of the constant
renc(local i)     = 0x32 ‖ u64(i)             -- member i of the block being hashed (§9)
renc(byName n)    = 0x33 ‖ name(n)            -- unresolved (§10)
renc(leaf n)      = 0x34 ‖ xname(n)           -- the name as the reference: type_hash only (§15)
```

**Depth.** `depth` is 0 for `bvar`, `fvar`, `mvar`, `sort`, `const` and
`lit`. It is `1 + max` of the children's depths for `app`, `lam`,
`forallE` and `letE`, and `1 + depth(struct)` for `proj`. Lean computes
the same number as `Expr.approxDepth` on mdata-free terms; the cap at 255
does not matter, because only `depth ≤ 6` is ever tested.

**Node payloads** (tag and scalars), shared by both forms below:

| node | tag | scalars | children, in order |
|---|---|---|---|
| `bvar i` | `0x21` | `u64(i)` | — |
| `fvar x` | `0x22` | `name(x)` | — |
| `mvar m` | `0x23` | `name(m)` | — |
| `sort l` | `0x24` | `lvl(l)` | — |
| `const c [l₁…lₖ]` | `0x25` | `renc(R c) ‖ u64(k) ‖ lvl(l₁) ‖ … ‖ lvl(lₖ)` | — |
| `app f a` | `0x26` | — | `f`, `a` |
| `lam _ t b bi` | `0x27` | `u8(bi)` | `t`, `b` |
| `forallE _ t b bi` | `0x28` | `u8(bi)` | `t`, `b` |
| `letE _ t v b _` | `0x29` | — | `t`, `v`, `b` |
| `lit (natVal n)` | `0x2A` | `bignat(n)` | — |
| `lit (strVal s)` | `0x2B` | `str(s)` | — |
| `proj S i s` | `0x2C` | `renc(R S) ‖ u64(i)` | `s` |

`bi`: `default = 0`, `implicit = 1`, `strictImplicit = 2`, `instImplicit = 3`.

**Flat form**, for `depth(e) ≤ 6`:

```
⟦e⟧ = H( 0x2F ‖ flat(e) )
flat(e) = tag ‖ scalars ‖ flat(child₁) ‖ … ‖ flat(childₘ)      -- pre-order
```

**Merkle form**, for `depth(e) > 6`:

```
⟦e⟧ = H( tag ‖ scalars ‖ ⟦child₁⟧ ‖ … ‖ ⟦childₘ⟧ )
```

The threshold is part of the identity: the two forms give different
digests for the same term. A child of a Merkle node takes the flat form
whenever its own depth is ≤ 6. Implementations SHOULD memoise `⟦·⟧` on
structurally equal subterms. Proof terms are DAGs with exponentially
large trees, and the memo is what keeps hashing linear in the DAG.

## 8. Declaration encodings

Kind tags: `axiom 1`, `defn 2`, `thm 3`, `opaque 4`, `quot 5`,
`induct 6`, `ctor 7`, `rec 8`. Safety: `safe 0`, `unsafe 1`,
`partial 2`. Quotient kinds: `type 0`, `ctor 1`, `lift 2`, `ind 3`.
Booleans are `u8` 0/1. `⟦·⟧` below is always taken over the
canonicalised expression (§6) under the current resolver `R`.

```
stmt_R(c) = H( 0xA1 ‖ v ‖ u64(#levelParams) ‖ ⟦type⟧ )

tail_R(c) =
  axiom   : u8(isUnsafe)
  defn    : u8(safety) ‖ ⟦value⟧
  thm     : ⟦value⟧                         (empty in statement mode, §11)
  opaque  : u8(isUnsafe) ‖ ⟦value⟧
  quot    : u8(quotKind)
  induct  : u64(numParams) ‖ u64(numIndices) ‖ u64(numNested) ‖ u8(isRec) ‖ u8(isUnsafe)
            ‖ u8(isReflexive) ‖ u64(#ctors) ‖ renc(R ctor₀) ‖ … ‖ renc(R ctorₙ₋₁)
  ctor    : renc(R induct) ‖ u64(cidx) ‖ u64(numParams) ‖ u64(numFields) ‖ u8(isUnsafe)
  rec     : u64(numParams) ‖ u64(numIndices) ‖ u64(numMotives) ‖ u64(numMinors) ‖ u8(k)
            ‖ u8(isUnsafe) ‖ u64(#rules) ‖ for each rule: renc(R ctor) ‖ u64(nfields) ‖ ⟦rhs⟧

member_R(c) = u8(kind) ‖ stmt_R(c) ‖ tail_R(c)
```

Constructors and rules are encoded in their stored order.

## 9. The reference graph, blocks, and the three ids

### 9.1 References

`refs(c)` is the set of names `c` depends on:

- every `const` name in `type`, and in `value` for `defn`, `opaque` and
  `thm` (not for `thm` in statement mode, §11);
- `induct`: `ctors`, and `all` minus `c` itself;
- `ctor`: `induct`;
- `rec`: `all`, and each rule's `ctor` and the `const` names in its `rhs`;
- `defn`, `opaque`, `thm`: `all` minus `c` itself.

The type name inside a `proj` node is **not** a graph edge. It is still
resolved and encoded (§7). In a well-typed term the structure is
reachable through the term's other references, so it is identified
first.

### 9.2 Blocks

The strongly connected components (SCCs) of the graph `c → refs(c)` are
computed over the whole input. Edges to names outside the input are
ignored here; those names are resolved through the base table (§10). An
SCC is a **block** if it has more than one member or if its single
member is in its own `refs`; any other constant is **standalone**. SCCs
are processed so that every SCC comes after the SCCs it references. Each
constant's `ref` is added to the table as soon as its SCC is done.

Typical blocks:
- an inductive type with its constructors;
- a mutual family;
- the recursors of a nested or mutual family, which call one another;
- a self-recursive `_unsafe_rec`.

A non-nested recursor is standalone.

### 9.3 Standalone constants

With `R(n) = id(table[n])`:

```
stmt = stmt_R(c)
decl = H( 0xA2 ‖ v ‖ u8(kind) ‖ stmt ‖ tail_R(c) )
ref  = stmt if c is a thm, else decl
```

### 9.4 Blocks

Let `B` be the member set.

1. **Shape.** For each member `m`, `shape(m) = H(member_A(m))`, where
   `A(n) = local 0` for every `n ∈ B`, and `A(n) = id(table[n])` otherwise.
2. **Canonical order.** Sort members by `shape` ascending, compared as
   bytes lexicographically. Ties are broken by source position:
   - `induct`: `1000·idx(all, m)`;
   - `ctor`: `1000·idx(all of its induct, induct) + cidx + 1`;
   - `rec`: `1000·|all| + 900 + idx(all, prefix of m)`;
   - `defn`, `opaque`, `thm`: `idx(all, m)`.

   Here `idx` is the 0-based position, or the list's length if absent.
   A tie means the members' encodings are byte-identical, so the
   tie-break decides only which *name* gets which index. It never changes
   the block id. Call the ordered members `m₀ … mₙ₋₁`.
3. **Block id.** With `L(n) = local i` for `n = mᵢ`, and `id(table[n])`
   otherwise:
   ```
   block = H( 0xA3 ‖ v ‖ u64(n) ‖ member_L(m₀) ‖ … ‖ member_L(mₙ₋₁) )
   ```
4. **Member ids.**
   ```
   decl(mᵢ) = H( 0xA4 ‖ v ‖ block ‖ u64(i) )
   stmt(mᵢ) = stmt_F(mᵢ)   where F(n) = id(decl(n)) for n ∈ B, else id(table[n])
   ref(mᵢ)  = stmt(mᵢ) if mᵢ is a thm, else decl(mᵢ)
   ```
   Inside its own block, a sibling is referenced by its `decl`, even when
   the sibling is a theorem.

## 10. Resolution and unresolved references

The base table maps names to the `ref`s of constants already identified,
including all of the input's own SCCs as they complete. A name found
neither in the table nor in the current block is encoded as
`byName n`. An implementation MUST report every such name. The
resulting ids MUST NOT be presented as addresses, because they are
exact only relative to a naming convention. A cached subterm id that
involved a fallback MUST still report that fallback when reused.

To obtain exact ids for a library, identify its dependencies first. The
closure of any input under `refs` resolves completely; `Init` alone
gives 0 unresolved.

## 11. Statement mode

A computation MAY run in **statement mode**:
- theorem values are neither hashed nor followed as references;
- a theorem's `tail` is empty, so `decl(thm) = H(0xA2 ‖ v ‖ 0x03 ‖ stmt)`;
- `stmt` and `ref` of every constant are unchanged, except where a
  theorem's *proof* closes a cycle that makes it a block member (§13).

A registry or a dependent needs only these ids, and the cone they
require is much smaller.

## 12. Test vectors

Every id is given in base58. The two sets use different inputs.

**Set A.** Declarations that reference nothing outside their own block,
so the ids depend only on the scheme:

```lean
inductive T where | a | b
def idT (x : T) : T := x
```

| id | value |
|---|---|
| `decl(T)` | `AwbguQQn99uqMeaCaqyKHw57myYCFN8QxPuucQ8xeZTJ` |
| `decl(T.a)` | `39W2PKpM7xCyj9RyTYDNjnibqnAuCUqBJxgewcAvjYQK` |
| `stmt(T.rec)` | `6cqensD4yYH2bdFVSE3GAzBGexXV2M5NHCLiV4DjfAYD` |
| `decl(idT)` | `2L8HHtdHc1GnBSmsACbRew9etEWEo1y4ZnNhX8XjGn1N` |

`T.rec.{u} : {motive : T → Sort u} → motive T.a → motive T.b → (t : T) → motive t`
(the motive binder implicit, the others default).

**Set B.** Over this base table of `ref`s (Lean v4.35.0, hex):

```
Nat           7fb2a329273091b1cab1d0de5ae79287b656d4020e9aaf6f6cf5f8d2856abcef
Eq            b04c703d0fd427681207151d10bd619905146c4f2e566493ee5bc5a9621a74d9
HAdd.hAdd     21d224e41b0d36e25396c57f1d564e6dc0cbfc79fb01e0f8b0593f357709ca25
instHAdd      56e6e06da7817bade49ac08cf4dce572c72d97df527ed032daab175cf390cebe
instAddNat    1e73d434775b9fa30f6d65a3f35b8f02aab17f65ae3971b0992129295ee37538
OfNat.ofNat   90ec041fa5e8dde1f15d3897e134d66a439f76c61f05e4b2dd9a591ba833cd78
instOfNatNat  dd09eafbd1b3ad4621cd607b940fcc7475acab7e6c9c70323d56fdbed60e7fc0
```

| input | id | value | exercises |
|---|---|---|---|
| `Nat.add_zero : ∀ n : Nat, n + 0 = n` | `stmt` | `ByKFv4nqHrcsFWuBFd7ihUXKFNEdMvFdMvjW7n8XE3nn` | Merkle form (depth 9), literal `0` |
| `def big : Nat := 18446744073709551616` | `decl` | `qyC5XoBvrSDTbcPawy59p4fiT1VjSvamo8gK2JpVqX5` | `bignat` beyond 64 bits |
| `structure P where (x : Nat) (y : Nat)`: `P` | `decl` | `6PnwNkHkkfzYiTRZ4x4UUTERSjCf6xurDiChq8Rax7Kx` | block with one constructor |
| ditto, `P.mk` | `decl` | `kVBJfYjxoUkBgJ7gp694anFkxBtmdqNvbFP3QzHYJKo` | |
| `def P.swap (p : P) : P := ⟨p.2, p.1⟩`, with `P.x`, `P.y` **not** in the table | `decl` | `EaQQWNhTHis186MUGjrX12waDF2RGqJn85jojKQk3j7m` | `byName` fallback; unresolved = `{P.x, P.y}` |

The exact kernel terms are written out in `tools/refhash_ref.py`. Note
that `big`'s value is `@OfNat.ofNat Nat 18446744073709551616 (instOfNatNat 18446744073709551616)`,
not a bare literal. Set A is also pinned in Lean by
`lake exe refhash-test`.

**Set C** (`type_hash`, §15). Built from bare constants, so no
elaboration and no toolchain enters:
`Eq.{1} Nat e e` with `e₀ = Nat.zero` and `eₖ₊₁ = Nat.add eₖ eₖ`, 64
levels deep: a tree of 2⁶⁴ nodes, a DAG of 66.

| id | value (hex) |
|---|---|
| `type_hash` | `dda12a826db3b1b9a25cfc80c0fca6ef9fc272f925ae4907ff289c026bd9b3a1` |

An implementation that does not memoise (§7) cannot compute it. Pinned
in Lean by `lake exe refhash-test` and in `tools/refhash_ref.py`.

## 13. Known limits of scheme 1

These are properties of the scheme as specified, recorded so that nobody
mistakes them for implementation bugs. Fixing any of them changes ids
and needs a new scheme version.

1. **Tied to Lean's `Level.normalize`.** §5.2 restates Lean v4.35.0. If
   a future Lean changes that function, CA ids computed with it change
   too. A conforming implementation follows §5.2, not the Lean version
   it happens to link.
2. **The input set shapes blocks.** SCCs are computed over the input,
   and edges into the base table are ignored. If some members of a cycle
   are in the base table and others in the input, the result differs
   from computing the whole cycle at once. Callers MUST identify an SCC
   as a whole, which ingestion foundations-first does.
3. **Statement mode and proof cycles.** A theorem whose proof closes a
   reference cycle is a block member in full mode and standalone in
   statement mode. Its `stmt` can then differ between the two modes. How
   often this happens has not been measured.
4. **Siblings are referenced by `decl`.** Inside a block, a theorem
   sibling is embedded by its `decl` (§9.4), not by its `stmt`, so
   re-proving a theorem that sits in a mutual block changes its
   siblings' ids.
5. **Elaboration, not source.** Ids are of kernel terms. A change in
   elaboration (instance paths, auxiliary-definition naming, `match`
   compilation) across Lean versions changes ids even when the source
   is unchanged. Measured on a sample of 300 Mathlib names, v4.33 → v4.35:
   75% of `decl` ids changed, most of them through dependencies.

## 14. Versioning

Every top-level preimage starts with a domain tag (`0xA1` `STMT`, `0xA2`
`DECL`, `0xA3` `BLOCK`, `0xA4` `MEMBER`) followed by `v`, or by `w` for
`0xA5` `TYPEHASH` (§15). Expression
node tags (`0x2*`), level tags (`0x1*`) and reference tags (`0x3*`) are
disjoint from these and from one another, so no two kinds of preimage
can coincide.

A change to any byte of any encoding in this document requires a new
`v`. Stores and registries record the scheme they were built with (CA:
`ca_scheme_version` in `meta.json`) and MUST NOT compare ids across
schemes.

| scheme | CA release | change |
|---|---|---|
| 0 | pre-release development | no version byte; literals truncated to 64 bits; levels hashed syntactically |
| 1 | v0.1.0 and later | this document |

## 15. The name-based statement hash (`type_hash`, scheme 2)

`type_hash` identifies a statement with its constants **by name**: the
coarse handle that survives a toolchain release (`ref-hash.md`, *Which
id to use where*). It is not an address. Equal `type_hash` with
different `stmt` means one name, two meanings.

```
type_hash(c) = H( 0xA5 ‖ w ‖ u64(#levelParams) ‖ ⟦type c⟧_leaf )
```

- `w = 0x02` is the `type_hash` scheme, versioned apart from `v`.
- `⟦·⟧_leaf` is §7 with the resolver mapping **every** constant, the
  structure of a `proj` included, to `leaf n` (`0x34 ‖ xname(n)`). There
  are no blocks, no base table and no fallbacks. A `leaf` is the
  intended encoding, not an unresolved reference (§10).
- The canonical form is §6's, from the declaration's `levelParams`,
  exactly as for `stmt`.
- The flat/Merkle split and the memo of §7 apply unchanged, so the cost
  is the size of the DAG.

**Scheme 1** (CA v0.1.0 to v0.3.1, `CA.ExprHash`) was SHA-256 over a
flat pre-order serialisation of the whole tree, with constants by
`name(n)` and universe parameters renamed per expression. Its cost was
the size of the tree, and statements whose DAG has about 10³ nodes and
whose tree has more than 10⁸ took tens of GB (`ref-hash.md`). Scheme 1
and scheme 2 values MUST NOT be compared. A registry or node file that
publishes `type_hash` MUST record its scheme (`type_hash_scheme`); one
that does not record it is scheme 1.

Test vector: §12, set C.

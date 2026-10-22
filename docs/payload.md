# CA payloads — the stored form of a declaration (draft)

Status: **draft 1, not normative** (2026-10-22). This document defines
the bytes a registry node stores for a declaration, so that

1. anyone can recompute the declaration's ids from them with
   [`spec.md`](spec.md) §5–§10 alone, with no Lean and without the
   rest of the cone (references are already ids); and
2. a Lean implementation can rebuild a `ConstantInfo` the kernel treats
   exactly as the original.

It is the payload of the SQLite node file
([`registry-protocol.md`](registry-protocol.md) §4, §12). Payloads are
not ids: this format has its own version byte `p` (`0x01` here) and can
change without changing any id. The key words MUST, MUST NOT, SHOULD and
MAY are used as in RFC 2119.

## 1. Shape: three parts

| part | keyed by | holds | covered by the ids |
|---|---|---|---|
| **ref table** | position in the file | the 32-byte `ref` of every constant the file's units mention | yes, through §7 `renc` |
| **unit** | `decl` (standalone) or `block` | the canonical declaration(s): kind, structural fields, canonical terms as one shared node table | yes: the ids are computed from it |
| **decoration** | (`decl`, name) | what canonicalisation erases: names, binder names, universe parameter names, reducibility hints, `nonDep` flags | **no** |

The split follows the line `spec.md` §4 draws: everything the ids read
is in the unit, everything they ignore is in the decoration. Two
consequences:

- **A decoration cannot change what a declaration means.** Whatever it
  says, the unit and its ids are unchanged. A wrong or hostile
  decoration produces wrong names or slow unfolding, never a different
  theorem, so a reader checks units and may take decorations from
  anyone.
- **Twins need no special case.** Declarations equal up to renaming
  (`Add`/`Mul` families under `to_additive`) share one `decl` and one
  unit, and each has its own decoration. declbuild's `cinfo-named:` rows
  exist only because its payload format mixes the two.

## 2. Primitive encodings

In addition to `spec.md` §3:

| notation | encoding |
|---|---|
| `uv(n)` | unsigned LEB128: 7 bits per byte, low group first, high bit set on every byte but the last. MUST be minimal (no trailing `0x80` groups); `0` is `0x00` |
| `sv(s)` | `uv(len) ‖ UTF-8 of s` |

`uv` replaces `u64` everywhere in a payload. The ids still use `u64`:
a checker re-encodes when it hashes (§5).

## 3. Units

A **unit** is what the ids are computed over in one step: a standalone
constant (`spec.md` §9.3), a block (§9.4), or a statement with no
declaration behind it (a `Statement` object, `registry-protocol.md` §4).

```
unit     = u8(p) ‖ u8(form) ‖ refs ‖ nodes ‖ body
form     : 0 statement, 1 standalone, 2 block
refs     = uv(k) ‖ uv(t₀) ‖ … ‖ uv(tₖ₋₁)           -- positions in the file's ref table
nodes    = uv(m) ‖ node₀ ‖ … ‖ nodeₘ₋₁
body     = statement:  uv(#levelParams) ‖ uv(type)
           standalone: member
           block:      uv(n) ‖ member₀ ‖ … ‖ memberₙ₋₁   -- canonical order, spec.md §9.4
```

`refs` is the unit's own reference list. Nodes and fields cite a
reference by its position `j` in this list, which `tⱼ` maps into the
file's ref table (§6). Within a unit the list has no duplicates.

### 3.1 References inside a unit

```
rref = 0x30                 -- the member itself (a standalone constant's `all`)
     | 0x31 ‖ uv(j)         -- refs[j], i.e. renc(id ref-table[t_j])
     | 0x32 ‖ uv(i)         -- member i of this block (renc(local i))
     | 0x33 ‖ name(n)       -- unresolved, renc(byName n) (spec.md §10)
```

`0x31`–`0x33` mirror `spec.md` §7's `renc` with the id replaced by a
position. `0x30` occurs only in `all` fields, which `spec.md` reads as
graph edges but never encodes.

### 3.2 Nodes

The canonical terms of every member (`spec.md` §6: positional universe
names, normalised levels, no `mdata`) are written as one table. A node
is one of `spec.md` §7's node kinds:

| node | tag | fields |
|---|---|---|
| `bvar i` | `0x21` | `uv(i)` |
| `sort l` | `0x24` | `lv(l)` |
| `const c [l₁…lₖ]` | `0x25` | `rref(c) ‖ uv(k) ‖ lv(l₁) ‖ … ‖ lv(lₖ)` |
| `app f a` | `0x26` | `back(f) ‖ back(a)` |
| `lam _ t b bi` | `0x27` | `u8(bi) ‖ back(t) ‖ back(b)` |
| `forallE _ t b bi` | `0x28` | `u8(bi) ‖ back(t) ‖ back(b)` |
| `letE _ t v b _` | `0x29` | `back(t) ‖ back(v) ‖ back(b)` |
| `lit (natVal n)` | `0x2A` | `uv(len) ‖ big-endian bytes of n` (minimal; `0` is empty) |
| `lit (strVal s)` | `0x2B` | `sv(s)` |
| `proj S i s` | `0x2C` | `rref(S) ‖ uv(i) ‖ back(s)` |

`fvar` and `mvar` do not occur in kernel declarations and MUST NOT
occur in a unit. `back(c)` is `uv(self − c)` for the node at index
`self` citing child `c`, always `≥ 1`: children precede their parents.

Levels, after canonicalisation, use positions instead of names:

```
lv(zero) = 0x10   lv(succ l) = 0x11 ‖ lv(l)   lv(max a b) = 0x12 ‖ lv(a) ‖ lv(b)
lv(imax a b) = 0x13 ‖ lv(a) ‖ lv(b)           lv(param u_i) = 0x14 ‖ uv(i)
```

**One node per subterm, in a fixed order.** Two structurally equal
canonical subterms MUST be one node. The table is the post-order
traversal of the unit's root terms, children left to right, each
subterm emitted at its first occurrence. The roots are taken member by
member in body order, and within a member in field order (§3.3). The
unit is therefore a function of the canonical declarations alone: equal
units are equal bytes, and a payload digest compares them.

### 3.3 Members

```
member = u8(kind) ‖ uv(#levelParams) ‖ uv(type) ‖ fields(kind)

fields(axiom)  = u8(isUnsafe)
fields(defn)   = u8(safety) ‖ uv(value) ‖ all
fields(thm)    = u8(hasValue) ‖ [uv(value)] ‖ all      -- hasValue 0: statement mode (spec.md §11)
fields(opaque) = u8(isUnsafe) ‖ uv(value) ‖ all
fields(quot)   = u8(quotKind)
fields(induct) = uv(numParams) ‖ uv(numIndices) ‖ uv(numNested) ‖ u8(isRec) ‖ u8(isUnsafe)
                 ‖ u8(isReflexive) ‖ uv(#ctors) ‖ rref… ‖ all
fields(ctor)   = rref(induct) ‖ uv(cidx) ‖ uv(numParams) ‖ uv(numFields) ‖ u8(isUnsafe)
fields(rec)    = uv(numParams) ‖ uv(numIndices) ‖ uv(numMotives) ‖ uv(numMinors) ‖ u8(k)
                 ‖ u8(isUnsafe) ‖ uv(#rules) ‖ (rref(ctor) ‖ uv(nfields) ‖ uv(rhs))… ‖ all
all            = uv(#all) ‖ rref…
```

`type`, `value` and `rhs` are node indices. Kind, safety and quotient
tags are `spec.md` §8's.

`all` is in the unit, not the decoration: it is a graph edge
(`spec.md` §9.1), so it decides which constants form a block, and with
that the ids.

A **statement unit** (form 0) is the type of a theorem without the
theorem. Its `stmt` equals the `stmt` of any theorem with that type
(`spec.md` §8). It is how a node holds an open statement, or a
statement whose proofs it does not keep.

## 4. Decorations

A decoration rebuilds one named declaration from its unit. For a block
there is one decoration per member and name.

```
decoration = u8(p) ‖ name(own) ‖ uv(member)
             ‖ uv(k) ‖ nameRef₀ ‖ … ‖ nameRefₖ₋₁        -- one per entry of the unit's refs
             ‖ uv(#levelParams) ‖ name(p₀) ‖ … ‖ name(pₙ₋₁)
             ‖ binders ‖ lets ‖ hints
nameRef    = uv(position in the file's name table)
binders    = uv(#table) ‖ sv(s₀) ‖ … ‖ uv(#b) ‖ uv(ix₀) ‖ … ‖ uv(ixᵦ₋₁)
lets       = ⌈#letE / 8⌉ bytes, bit i = nonDep of the i-th letE node
hints      = defn only: 0x00 opaque | 0x01 abbrev | 0x02 ‖ uv(height)
```

`member` is the member's index in the block (`0` for a standalone
constant). `binders` gives one name per `lam`, `forallE` and `letE`
node of the unit, in node order, through a local string table. `lets`
counts `letE` nodes in node order. A reader rebuilds the
`ConstantInfo` by replacing each `0x31` reference with the name its
`nameRef` gives, `0x32 i` with the own name of member `i`'s decoration,
`0x30` with `own`, `u_i` with `pᵢ`, and each binder with its name.

### 4.1 What a rebuild does not restore

The unit shares structurally equal canonical subterms, so a node used
in two places carries one binder name. Where the original had two
different names there (`fun x => …` and `fun y => …` over the same
body), the rebuild uses the first. Levels come back normalised
(`spec.md` §5.2), and `mdata` is not stored.

None of this reaches the kernel: binder names and `mdata` are not
inspected, and a normalised level is equivalent to the original. A
rebuilt declaration therefore type-checks iff the original does, and
recomputing its ids gives back the unit's. It is not always byte-equal
to the `.olean`'s `ConstantInfo`; §8 lists what an exact round trip
would cost.

## 5. Checking a unit

A checker recomputes ids from a unit and the file's ref table:

1. Decode the nodes. For each, compute `depth` (`spec.md` §7) from its
   children.
2. Compute `⟦·⟧` bottom-up over the table: the flat form for
   `depth ≤ 6`, the Merkle form otherwise, re-encoding scalars with
   `spec.md` §3's primitives and resolving `rref`s as `renc`s through
   the ref table. Each node is hashed once, so the work is linear in the
   unit.
3. Statement unit: `stmt = H(0xA1 ‖ v ‖ u64(#levelParams) ‖ ⟦type⟧)`.
   Standalone: `spec.md` §9.3. Block: compute every member's shape
   (§9.4, `local 0` for all members), and reject the unit unless the
   members are in ascending shape order; then the block id, member
   `decl`s and `stmt`s as in §9.4.
4. Compare with the key the unit is filed under. A unit that contains
   `0x33` references is inexact (`spec.md` §10) and is reported as such.

A checker needs no Lean and no other unit: references are ids already.
Checking that a referenced id exists, or that the declaration is
well-typed, is a separate act (`registry-protocol.md` §5).

## 6. Files

In the SQLite node file (`registry-protocol.md` §12):

```
refs        (ix PK, ref)                  -- the file's ref table: 32-byte ids
names       (ix PK, name)                 -- the file's name table
units       (key PK, form, bytes)         -- key: decl (standalone), block id (block), stmt (statement)
members     (decl PK, unit, member)       -- every decl → its unit and index
decorations (decl, name, bytes, PK(decl, name))
```

`refs` and `names` are per file: a unit cites positions, so the same id
or name is stored once per file, not once per use. Positions are local
to the file; merging two files renumbers them, and units are
re-encoded (their bytes change, their ids do not). A unit MAY be stored
zstd-compressed, with or without a dictionary from the file's `dicts`
table; compression is a storage choice and not part of the unit.

## 7. Measured size

declbuild's `payload-probe` (2026-10-22) encoded 4,827 random Mathlib
v4.35.0 declarations in this shape and compared them with declbuild's
own payload (a serialised `ConstantInfo` with deduplicated names, no
subterm sharing), all zstd-compressed:

| layout | size | vs declbuild, no dictionary | vs declbuild, as stored (dictionary) |
|---|---|---|---|
| declbuild payload | 3.92 MB | 100% | 113% |
| units + decorations, ids inline in every unit | 9.01 MB | 230% | 259% |
| units + decorations, file ref and name tables (§6) | 5.13 MB | 131% | 148% |

- **The ids are the cost.** Inline, 32-byte ids are 44% of the
  uncompressed units and do not compress. The sample has 124,736
  reference uses and 25,287 distinct references; the per-file tables of
  §6 exist because of this measurement.
- **The sample understates the tables' benefit.** In a node file holding
  a whole library, the ref table has about one entry per declaration,
  while units grow linearly. Extrapolated, about 110% of declbuild's
  payload without a dictionary and 125% with one. A dictionary trained
  on units should recover part of that; it is worth about 11% on
  declbuild's payloads.
- **Decorations are about 20% of the compressed total**, mostly binder
  names.
- **Sharing subterms matters before compression.** The node tables total
  9.1 MB against 49.7 MB of declbuild's uncompressed payloads; on the
  largest declarations the ratio is about 100 to 1
  (`AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified`: 394 KB vs
  3.8 KB).

The probe used the field layout of this document with two
approximations: ref positions of realistic width, and binder names
counted over the original terms rather than the shared nodes.

## 8. Open questions

- **Exact round trip.** Restoring the original levels, `mdata` and
  binder names that differ on a shared node needs a list of node splits
  in the decoration. Measure first how many declarations differ at all
  (levels changed by normalisation, binder names in conflict on a shared
  node); if few, the splits are cheap.
- **A file as a unit of trust.** A unit is checkable only together with
  its file's ref table. A row copied out of a file must take the
  entries it cites, re-numbered. Whether a single-unit transport
  (HTTP range reads of one row) should instead carry ids inline, the
  230% layout, is open.
- **Extension state.** Simp sets, instances and attributes are not in a
  payload (`registry-protocol.md` §16, *Extension state*).
- **Test vectors.** None yet. The plan: the units and decorations of
  `spec.md` §12's Set A and Set B, with `tools/refhash_ref.py` extended
  to decode a unit and reproduce the ids from it.

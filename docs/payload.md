# CA payloads — the stored form of a declaration (draft)

Status: **draft 2, not normative** (2026-10-22). Implemented by
`CA.Payload` and tested by `lake exe payload-test`, which round-trips
every declaration of `Init` (§7); `ca pack` and `ca check` write and
check node files in the §6 layout (`cli/tests/node-test.sh`). This document defines the bytes a
registry node stores for a declaration, so that

1. anyone can recompute the declaration's ids from them with
   [`spec.md`](spec.md) §5–§10 alone, with no Lean and without the
   rest of the cone (references are already ids); and
2. a Lean implementation can rebuild exactly the declaration that was
   stored, up to level normalisation and `mdata` (§4.1).

It is the payload of the SQLite node file
([`registry-protocol.md`](registry-protocol.md) §4, §12). Payloads are
not ids: this format has its own version byte `p` (`0x01` here) and can
change without changing any id. The key words MUST, MUST NOT, SHOULD and
MAY are used as in RFC 2119.

## 1. Shape: three parts

| part | keyed by | holds | read by the ids |
|---|---|---|---|
| **ref table** | position in the file | the 32-byte `ref` of every constant the file's units mention | yes, through §7 `renc` |
| **unit** | the declaration's key (`decl`, block id or `stmt`) and its naming variant | the canonical declaration(s) with every name replaced by a numbered slot | yes: the ids are computed from it |
| **decoration** | (`decl`, name) | the names behind the slots, universe parameter names, reducibility hints | **no** |

A unit is the declaration with its names taken out but their **pattern**
kept. Every distinct constant name gets a reference slot and every
distinct binder name a binder slot. Two occurrences share a slot exactly
when they had the same name, and the decoration says which name each
slot stands for.

The pattern has to stay in the unit. CA's ids never see names, so
structurally identical constants share an id: `HAdd.hAdd` and
`HSub.hSub`, `LE.le` and `LT.lt`, `Add` and `Mul`. A term using `+` and
`-` mentions one id twice under two names. If the unit kept only the id,
the rebuild could restore only one of the names, and the rebuilt term
would no longer type-check. In `Init`, 13,660 of 65,180 units mention
some id under two names.

Consequences:

- **A decoration cannot change what a declaration means.** It only
  names slots. Whatever it says, the unit and its ids are unchanged. A
  wrong decoration produces a declaration with wrong names, which a
  kernel check then rejects; it can never make a different theorem pass
  as this one.
- **Twins share a unit.** Declarations equal up to a consistent renaming
  (`Add`/`Mul` families under `to_additive`) have one unit and one
  decoration each.
- **One key can hold more than one unit.** Two declarations can have the
  same id while their naming patterns differ: one uses `+` twice, the
  other `+` and `-`, over structures that are otherwise equal. They get
  different units under one key, called *naming variants*, and each
  variant checks to the same ids. In `Init`, 158 of 55,594 keys have
  more than one (0.3%). A node stores variants side by side (§6).

## 2. Primitive encodings

In addition to `spec.md` §3:

| notation | encoding |
|---|---|
| `uv(n)` | unsigned LEB128: 7 bits per byte, low group first, high bit set on every byte but the last. MUST be minimal (no trailing `0x80` groups); `0` is `0x00` |
| `sv(s)` | `uv(len) ‖ UTF-8 of s` |
| `nm(n)` | a Lean `Name`, root component first: `uv(#components)`, then `0x00 ‖ sv(s)` per string component and `0x01 ‖ uv(k)` per numeric one |
| `u8b(x)` | a boolean, one byte `0` or `1` |

`uv` replaces `u64` everywhere in a payload. The ids still use `u64`:
a checker re-encodes when it hashes (§5). `nm` is exact for every name,
including private and hygienic ones, where a dotted rendering is not.

## 3. Units

A **unit** is what the ids are computed over in one step: a standalone
constant (`spec.md` §9.3), a block (§9.4), or a statement with no
declaration behind it (a `Statement` object, `registry-protocol.md` §4).

```
unit     = u8(p) ‖ u8(form) ‖ refs ‖ nodes ‖ body
form     : 0 statement, 1 standalone, 2 block
refs     = uv(k) ‖ uv(t₀) ‖ … ‖ uv(tₖ₋₁)           -- one per reference slot: a position in the file's ref table
nodes    = uv(m) ‖ node₀ ‖ … ‖ nodeₘ₋₁
body     = statement:  uv(#levelParams) ‖ uv(type)
           standalone: member
           block:      uv(n) ‖ member₀ ‖ … ‖ memberₙ₋₁   -- canonical order, spec.md §9.4
```

`refs` lists the unit's reference slots, numbered by first occurrence.
Slot `j` stands for the id at file position `tⱼ`. Two slots MAY name the
same position; that is the case of two names sharing an id.

### 3.1 References inside a unit

```
rref = 0x30                 -- the member itself (a standalone constant's `all`)
     | 0x31 ‖ uv(j)         -- reference slot j: renc(id ref-table[t_j])
     | 0x32 ‖ uv(i)         -- member i of this block: renc(local i)
     | 0x33 ‖ nm(n)         -- unresolved, renc(byName n) (spec.md §10)
```

`0x31`–`0x33` mirror `spec.md` §7's `renc`, with the id replaced by a
slot. `0x30` occurs only in `all` fields, which `spec.md` reads as graph
edges but never encodes.

### 3.2 Nodes

The canonical terms of every member are written as one table
(`spec.md` §6: positional universe names, normalised levels, no
`mdata`). Each node is one of `spec.md` §7's node kinds:

| node | tag | fields |
|---|---|---|
| `bvar i` | `0x21` | `uv(i)` |
| `sort l` | `0x24` | `lv(l)` |
| `const c [l₁…lₖ]` | `0x25` | `rref(c) ‖ uv(k) ‖ lv(l₁) ‖ … ‖ lv(lₖ)` |
| `app f a` | `0x26` | `back(f) ‖ back(a)` |
| `lam x t b bi` | `0x27` | `u8(bi) ‖ uv(slot x) ‖ back(t) ‖ back(b)` |
| `forallE x t b bi` | `0x28` | `u8(bi) ‖ uv(slot x) ‖ back(t) ‖ back(b)` |
| `letE x t v b nd` | `0x29` | `uv(slot x) ‖ u8b(nd) ‖ back(t) ‖ back(v) ‖ back(b)` |
| `lit (natVal n)` | `0x2A` | `uv(len) ‖ big-endian bytes of n` (minimal; `0` is empty) |
| `lit (strVal s)` | `0x2B` | `sv(s)` |
| `proj S i s` | `0x2C` | `rref(S) ‖ uv(i) ‖ back(s)` |

`slot x` is the binder slot of the binder's name, numbered by first
occurrence. `nd` is `letE`'s `nonDep` flag. `fvar` and `mvar` do not
occur in kernel declarations and MUST NOT occur in a unit. `back(c)` is
`uv(self − c)` for the node at index `self` citing child `c`, always
`≥ 1`: children precede their parents.

Levels, after canonicalisation, use positions instead of names:

```
lv(zero) = 0x10   lv(succ l) = 0x11 ‖ lv(l)   lv(max a b) = 0x12 ‖ lv(a) ‖ lv(b)
lv(imax a b) = 0x13 ‖ lv(a) ‖ lv(b)           lv(param u_i) = 0x14 ‖ uv(i)
```

**One node per subterm, in a fixed order.** Two subterms whose nodes
would have equal fields (same tag, scalars, slots and children) MUST be
one node. The table is the post-order traversal of the unit's root
terms, children left to right, each node emitted at its first
occurrence. Roots are taken member by member in body order, and within a
member in field order (§3.3). Slots are numbered in the same traversal.
A unit is therefore a function of the declarations up to a consistent
renaming, and a digest of its bytes compares two units.

### 3.3 Members

```
member = u8(kind) ‖ uv(#levelParams) ‖ uv(type) ‖ fields(kind)

fields(axiom)  = u8b(isUnsafe)
fields(defn)   = u8(safety) ‖ uv(value) ‖ all
fields(thm)    = u8b(hasValue) ‖ [uv(value)] ‖ all     -- hasValue 0: statement mode (spec.md §11)
fields(opaque) = u8b(isUnsafe) ‖ uv(value) ‖ all
fields(quot)   = u8(quotKind)
fields(induct) = uv(numParams) ‖ uv(numIndices) ‖ uv(numNested) ‖ u8b(isRec) ‖ u8b(isUnsafe)
                 ‖ u8b(isReflexive) ‖ rrefs(ctors) ‖ all
fields(ctor)   = rref(induct) ‖ uv(cidx) ‖ uv(numParams) ‖ uv(numFields) ‖ u8b(isUnsafe)
fields(rec)    = uv(numParams) ‖ uv(numIndices) ‖ uv(numMotives) ‖ uv(numMinors) ‖ u8b(k)
                 ‖ u8b(isUnsafe) ‖ uv(#rules) ‖ (rref(ctor) ‖ uv(nfields) ‖ uv(rhs))… ‖ all
all            = rrefs(all)
rrefs(xs)      = uv(#xs) ‖ rref(x₀) ‖ …
```

`type`, `value` and `rhs` are node indices. Kind, safety and quotient
tags are `spec.md` §8's. A unit mixes theorems with and without values
only as an error: statement mode applies to the whole unit.

`all` is in the unit, not the decoration: it is a graph edge
(`spec.md` §9.1), so it decides which constants form a block, and with
that the ids.

A **statement unit** (form 0) is the type of a theorem without the
theorem. Its key is the `stmt` of any theorem with that type
(`spec.md` §8). It is how a node holds an open statement, or a
statement whose proofs it does not keep.

## 4. Decorations

A decoration names one member of a unit. For a block there is one per
member and name.

```
decoration = u8(p) ‖ nm(own) ‖ uv(member)
             ‖ uv(k) ‖ uv(n₀) ‖ … ‖ uv(nₖ₋₁)          -- a name-table position per reference slot
             ‖ uv(#levelParams) ‖ nm(p₀) ‖ …
             ‖ uv(#binderSlots) ‖ nm(x₀) ‖ …
             ‖ hints
hints      = 0xFF none | 0x00 opaque | 0x01 abbrev | 0x02 ‖ uv(height)    -- definitions carry one
```

`member` is the member's index in the block (`0` for a standalone
constant). To rebuild a `ConstantInfo`, a reader names reference slot
`j` with file name `nⱼ`, `0x32 i` with member `i`'s `own`, `0x30` with
`own`, universe position `i` with `pᵢ`, and binder slot `s` with `xₛ`.

### 4.1 What a rebuild restores

Everything the kernel and the elaborator read: constant names, binder
names and binder info, `nonDep`, hints, universe parameter names, every
structural field. Two things come back changed, and both are invisible to
the kernel:

- **Levels are normalised** (`spec.md` §5.2). A normalised level is
  equivalent to the original.
- **`mdata` is gone.** The kernel ignores it.

So a rebuilt declaration type-checks exactly when the original does,
and recomputing its ids gives back the unit's. `lake exe payload-test`
compares every rebuilt `Init` declaration with the original, names
included: all 65,180 units come back exactly.

## 5. Checking a unit

A checker recomputes ids from a unit and the file's ref table:

1. Decode the nodes. For each, compute `depth` (`spec.md` §7) from its
   children.
2. Compute `⟦·⟧` bottom-up over the table: the flat form for
   `depth ≤ 6`, the Merkle form otherwise. Scalars are re-encoded with
   `spec.md` §3's primitives, reference slots resolve to the ids they
   point at, and binder slots and `nonDep` are dropped. Each node is
   hashed once, so the work is linear in the unit.
3. Statement unit: `stmt = H(0xA1 ‖ v ‖ u64(#levelParams) ‖ ⟦type⟧)`.
   Standalone: `spec.md` §9.3. Block: compute every member's shape
   (§9.4, `local 0` for all members); the unit MUST list members in
   that order; then the block id, member `decl`s and `stmt`s as in §9.4.
4. Compare with the key the unit is filed under. A unit that contains
   `0x33` references is inexact (`spec.md` §10) and is reported as such.

A checker needs no Lean and no other unit: references are ids already.
Checking that a referenced id exists, or that the declaration is
well-typed, is a separate act (`registry-protocol.md` §5).

`CA.Payload.checkUnit` does this by rebuilding the members with
placeholder names and running `CA.RefHash.computeIds` on them, so the
check is the id computation itself rather than a second implementation
of it. `tools/registry_ref.py` (Python standard library, written from
this document and `spec.md`) follows the steps above directly over the
node table. The two agree on every unit of an `Init` node file (55,757
units, about 30 s each) and on §9's vectors.

## 6. Files

In the SQLite node file (`registry-protocol.md` §12):

```
refs        (ix PK, ref)                          -- the file's ref table: 32-byte ids
names       (ix PK, name, display)                -- the file's name table: nm-encoded, plus the dotted rendering
units       (id PK, key, variant, form, bytes, UNIQUE(key, variant))   -- variant: SHA-256 of bytes
members     (decl, name → names, unit → units, member, PK(decl, name))
decorations (decl, name → names, bytes, UNIQUE(decl, name))
```

A statement unit (an entry's) has one decoration keyed `(stmt, entry
name)` and no member row: it is what lets a reader rebuild the statement
with its names, to assume it (`ca verify`).

A `decl` has one row in `members` per name it is bound to. The row
points at the unit variant that name's declaration encodes to, so twins
point at one variant and naming variants at their own. Names, including
those of members, decorations and entries, are stored once in `names`
and cited by position; members cite their unit by row id. (Large rows
are kept out of `WITHOUT ROWID` tables: with them the `Init` file was
171 MB instead of 114 MB.) `ca pack` writes this file and `ca check`
checks it ([cli.md](cli.md)).

`refs` and `names` are per file: units cite positions, so each id and
name is stored once per file, not once per use. Positions are local to
the file. Merging two files renumbers them and re-encodes units: the
bytes change, the variant digest is recomputed, the ids do not. A unit
MAY be stored zstd-compressed, with or without a dictionary from the
file's `dicts` table. Compression is a storage choice, not part of the
unit.

## 7. Measured

**Round trip, `Init` (Lean v4.35.0; `lake exe payload-test`).**
- 66,025 constants; 65,180 units (1,200 blocks).
- Every unit checks to its original ids from its bytes alone.
- Every unit and decoration re-serialises to the same bytes.
- Every member rebuilds exactly, and the rebuilt declarations recompute
  the same ids.
- Totals: units 50.7 MB and decorations 17.7 MB, uncompressed. The file
  table holds 36,097 refs and 43,482 names. 158 keys have naming
  variants.

**Full mode against statement mode, `Init` (2026-10-23, `tools/measure.sh A`).**
The same 65,972 declarations packed with proofs (`--all`) and without
(`--all --no-proofs`): `stmt` agrees on 65,972 of 65,972, `ref` on every
theorem (45,494) and every non-theorem (20,478). Statement mode changes
no id a dependent can see; it drops 839 units (proof-only auxiliaries),
22,000 refs and 27,000 names from the file, and packs in 89 s instead of
160 s (before the encoder stopped recomputing ids; a full pack is now
53 s, 47 s with `--fast`, file 121 MB, checked in 32 s). The `deps` table, when written (`--deps`), is 1,156,596 rows on
`Init`, more bytes than the units; it is derivable from them and off by
default.

**Size against declbuild's payload, Mathlib.** declbuild's
`payload-probe` (2026-10-22) encoded 4,827 random Mathlib v4.35.0
declarations in draft 1's shape (without name slots), all
zstd-compressed:

| layout | size | vs declbuild, no dictionary | vs declbuild, as stored (dictionary) |
|---|---|---|---|
| declbuild payload | 3.92 MB | 100% | 113% |
| units + decorations, ids inline in every unit | 9.01 MB | 230% | 259% |
| units + decorations, file ref and name tables (§6) | 5.13 MB | 131% | 148% |

On `Init`, name slots moved about 4% of the bytes from decorations into
units and left the total about the same; the probe has not been rerun
with them yet.

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
- **Sharing subterms matters before compression.** The node tables total
  9.1 MB against 49.7 MB of declbuild's uncompressed payloads; on the
  largest declarations the ratio is about 100 to 1
  (`AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified`: 394 KB vs
  3.8 KB).

## 8. Open questions

- **Families of twin blocks.** A block with twin names (`Add`/`Add.mk`
  and `Mul`/`Mul.mk` on one unit) has one decoration per member and
  name, but nothing says which decorations belong together. `CA.Verify`
  aligns them by sorted name and checks the result (constructors name
  their inductive, `all` lists match); a decoration could instead carry
  a family tag.
- **Original levels and `mdata`.** Restoring them exactly would need a
  per-node override in the decoration. Neither reaches the kernel; it
  matters only if a byte-identical `.olean` is ever the goal.
- **A unit read alone.** A unit is checkable only together with its
  file's ref table. A row copied out of a file must take the entries it
  cites, renumbered. Whether a single-unit transport (HTTP range reads
  of one row) should instead carry ids inline, the 230% layout, is open.
- **Extension state.** Simp sets, instances and attributes are not in a
  payload (`registry-protocol.md` §16, *Extension state*).
- **Decoration vectors.** §9 now pins six decorations as well; more
  (hints `abbrev` / `opaque`, universe-polymorphic binders) would help.

## 9. Test vectors

Units from `spec.md` §12's examples, as written by `ca pack` (Lean
v4.35.0, scheme 1, payload format 1), with their reference slots
renumbered `0…k-1` so each vector is self-contained: `refs` lists the id
behind each slot, in order. Decoding a unit and recomputing its ids as
in §5 must give `expect`: the unit's key, then the ids named in
`members` (`i,j`: member `i`, and `j` = 0 `stmt`, 1 `decl`, 2 `ref`).
The member ids are `spec.md` §12's golden values; the block id of `T` is
new here. `python3 -I tools/registry_ref.py --vectors` checks all four.

```text
name: inductive T (block T.a, T, T.b; spec.md Set A)
refs:
unit: 0102000225320100241110030700003201000000000600010000000000000232003202013201070000320101000000
members: 0,1 1,1
expect: 6DDpCR3D7KYqmYRC6moj6BDzUbB6dStcvUkg4y11aevB 39W2PKpM7xCyj9RyTYDNjnibqnAuCUqBJxgewcAvjYQK AwbguQQn99uqMeaCaqyKHw57myYCFN8QxPuucQ8xeZTJ
```

```text
name: T.rec (standalone; spec.md Set A)
refs: AwbguQQn99uqMeaCaqyKHw57myYCFN8QxPuucQ8xeZTJ 39W2PKpM7xCyj9RyTYDNjnibqnAuCUqBJxgewcAvjYQK HXoucYvHwNNdQ18f52gCPdNBB1z6PGC3M2ieVM3KMGwh
unit: 0101030001021525310000241400280001020121002531010026020121012531020026020121032601072800010b01280003040128000208012801000c0127000307092700020b012700000f012700030a0f2700020e01270000120108010e000001020000023101001131020014013100
members: 0,0
expect: E12cVn4293JnFftV3PpDQtt7Eb6WbphwUkmXg12dfqgn 6cqensD4yYH2bdFVSE3GAzBGexXV2M5NHCLiV4DjfAYD
```

```text
name: idT (standalone; spec.md Set A)
refs: AwbguQQn99uqMeaCaqyKHw57myYCFN8QxPuucQ8xeZTJ
unit: 01010100042531000028000001012100270000030102000100030130
expect: 2L8HHtdHc1GnBSmsACbRew9etEWEo1y4ZnNhX8XjGn1N
```

```text
name: ∀ n : Nat, n + 0 = n (statement unit; spec.md Set B, Nat.add_zero)
refs: 9bUmPmuYBLgXAzBq2ZWfqC4GTtS2habh6kKeA2KwLsCJ CsCMj6owGLa7e1vwzAoBCbq5mV5Bkg7LNUW4WecAGMoN 3H2JnCKuEaTitrkcLzGP8Mqk9aPWhAcJVzV2LjWgqq2U 6rEFXi3hyDWyTxWhhQzTnGoZFcFuQ3146MUiTdfZQYPF 33sftyMqxjE8r1YvonnZh1f68rNgaMxmi7t2yLQntpWb AkiSexvWpb4RP6NJTMidnYdyHynEPgTY7KBVPVwH3NVV Fsqscbcf7WGRoEZEMF17AavbX1bSu8b4KiFPbw5h8SCf
unit: 010007000102030405061925310000253101011110260102253102031010102601042601052601062531030110260108253104002602012605012100260201253105011026010f2a002602012531060026010326030126080126140126010b28000018010018
expect: ByKFv4nqHrcsFWuBFd7ihUXKFNEdMvFdMvjW7n8XE3nn
```

The `refs` of the last vector are the `ref`s of `Nat`, `Eq`, `HAdd.hAdd`,
`instHAdd`, `instAddNat`, `OfNat.ofNat` and `instOfNatNat` in slot
order (`spec.md` §12 lists the same ids in hex).

### Decorations

Decorations of the same declarations, as `ca pack` writes them, with the
name-table positions renumbered `0…k-1` in slot order so each vector is
self-contained (`slots` lists the name behind each position). Decoding
one (§4) must give the fields shown; `python3 -I tools/registry_ref.py
--vectors` and `lake exe node-test` check all six.

```text
name: inductive T, member T (block T.a, T, T.b)
key: AwbguQQn99uqMeaCaqyKHw57myYCFN8QxPuucQ8xeZTJ
slots: (none)
decoration: 010100015401000000ff
own: T  member: 1  levels: (none)  binders: (none)  hints: none
```
```text
name: T.a, member 0 of the block
key: 39W2PKpM7xCyj9RyTYDNjnibqnAuCUqBJxgewcAvjYQK
slots: (none)
decoration: 010200015400016100000000ff
own: T.a  member: 0  levels: (none)  binders: (none)  hints: none
```
```text
name: T.b, member 2 of the block
key: HXoucYvHwNNdQ18f52gCPdNBB1z6PGC3M2ieVM3KMGwh
slots: (none)
decoration: 010200015400016202000000ff
own: T.b  member: 2  levels: (none)  binders: (none)  hints: none
```
```text
name: T.rec (standalone)
key: E12cVn4293JnFftV3PpDQtt7Eb6WbphwUkmXg12dfqgn
slots: T T.a T.b
decoration: 0102000154000372656300030001020101000175040100066d6f74697665010001740100016101000162ff
own: T.rec  member: 0  levels: u  binders: motive t a b  hints: none
```
```text
name: idT (standalone)
key: 2L8HHtdHc1GnBSmsACbRew9etEWEo1y4ZnNhX8XjGn1N
slots: T
decoration: 010100036964540001000001010001780201
own: idT  member: 0  levels: (none)  binders: x  hints: regular 1
```
```text
name: statement unit of ∀ n : Nat, n + 0 = n (Nat.add_zero's statement), decoration named Conj
key: ByKFv4nqHrcsFWuBFd7ihUXKFNEdMvFdMvjW7n8XE3nn
slots: Nat Eq HAdd.hAdd instHAdd instAddNat OfNat.ofNat instOfNatNat
decoration: 01010004436f6e6a00070001020304050600010100016eff
own: Conj  member: 0  levels: (none)  binders: n  hints: none
```


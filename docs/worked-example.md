# The banner, computed by hand

Every value on the figure below, and the `stmt` on the [README banner](../README.md),
is produced by the library; here is how, step by step, for `Nat.add_zero` on Lean v4.35.0,
encoding scheme 1.
The ids are base58 renderings of 32-byte SHA-256 digests. The last
subsection is an `#eval` that reproduces every number.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="figure-stmt-dag-dark.svg?v=1">
  <img alt="The statement of Nat.add_zero embeds the ids of the seven constants it mentions; instHAdd and instAddNat embed the ids of their values Add.add and Nat.add; the proof is not part of the address" src="figure-stmt-dag-light.svg?v=1" width="100%">
</picture>

The figure is what this page computes: the statement's address embeds
the ids of the constants it mentions, a definition's id embeds its
value, and the proof is outside the address.

## 1. The input: the elaborated statement, nothing else

`Nat.add_zero` is a `theorem` with no universe parameters and this type
(`set_option pp.all true`):

```lean
∀ (n : Nat),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    n
```

This is the term exactly as the kernel stores it. No `whnf`, no
unfolding, no instance resolution happens anywhere below: `n + 0` stays
spelled through `HAdd.hAdd`, `instHAdd`, `instAddNat`, `OfNat.ofNat`
and `instOfNatNat`. The statement mentions seven constants, and those
are the seven tiles.

The proof, `fun n => Nat.add_zero n` on the banner and `rfl`-like
`Nat.rec` machinery in `Init`, is never read. A theorem's `ref` is its
`stmt`, and `stmt` is a function of the type alone.

## 2. Canonicalise (L0)

`canonicalizeL0Decl [] type`: the universe binder list is empty, so
nothing is renamed; the closed levels `1` and `0` are already in
`Level.normalize` form; there is no `mdata`. The canonical term is the
term above.

## 3. Resolve the seven references to their own ids

Each `.const` node is embedded by the referenced constant's `ref`, never
by its name. Those `ref`s come from the **statement cone**: the closure
of the statement under references, following types always and the
values of definitions, never proofs. For this statement the cone is 31
constants of `Init`, hashed foundations first:

| constant | kind | how its `ref` arises | `ref` |
|---|---|---|---|
| `Nat` | inductive | member 2 of the block `{Nat, Nat.zero, Nat.succ}`: `H(MEMBER ‖ 1 ‖ blockId ‖ 2)` | `9bUmPmuYBLg…` |
| `Eq` | inductive | member 1 of the block `{Eq, Eq.refl}` | `CsCMj6owGLa…` |
| `HAdd.hAdd` | definition (projection) | `decl`: kind, safety, `stmt`, and the value `fun α β γ [self : HAdd α β γ] => self.1`, whose `.proj` node embeds `ref(HAdd)` | `3H2JnCKuEaT…` |
| `instHAdd` | definition | `decl`, value `⟨fun a b => Add.add a b⟩` embeds `ref(Add.add)`, `ref(HAdd.mk)`, `ref(Add)` | `6rEFXi3hyDW…` |
| `instAddNat` | definition | `decl`, value `⟨Nat.add⟩` embeds `ref(Add.mk)`, `ref(Nat)`, `ref(Nat.add)` | `33sftyMqxjE…` |
| `OfNat.ofNat` | definition (projection) | as `HAdd.hAdd`, over `OfNat` | `AkiSexvWpb4…` |
| `instOfNatNat` | definition | `decl`, value `fun n => ⟨n⟩` | `Fsqscbcf7WG…` |

A definition's `ref` is its `decl`, which includes its value: that is
why `Nat.add` and `Add.add` sit under `instAddNat` and `instHAdd` on the
banner, and why redefining `Nat.add` would change this theorem's `stmt`
three levels up.

## 4. Merkle-hash the term

`exprId` gives every subterm a 32-byte id. A subterm whose `approxDepth`
is at most 6 is hashed **flat**, in one SHA-256 over its whole pre-order
serialisation prefixed by the tag `0x2F`; a deeper subterm is hashed
from the ids of its children, `H(tag ‖ scalars ‖ child ids)`. Depths
here:

```
∀ n : Nat, Eq Nat X n          depth 9   Merkle: H(0x28 ‖ binderInfo ‖ id(Nat) ‖ id(body))
├─ Nat                         depth 0   flat
└─ (Eq Nat X) n                depth 8   Merkle: H(0x26 ‖ id(Eq Nat X) ‖ id(bvar 0))
   ├─ (Eq Nat) X               depth 7   Merkle: H(0x26 ‖ id(Eq Nat) ‖ id(X))
   │  ├─ Eq Nat                depth 1   flat
   │  └─ X = HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) n (OfNat.ofNat Nat 0 (instOfNatNat 0))
   │                           depth 6   flat: one chunk holding five refs and the literal
   └─ bvar 0                   depth 0   flat
```

The flat chunk of the leaf `Nat` is 44 bytes:

```
2f                      flat chunk
25                      const
31 7fb2a329…abcef       reference encoded as id: ref(Nat), 32 bytes
00 00 00 00 00 00 00 00 number of universe levels, u64 little-endian: 0
```

and its SHA-256 is `id(Nat) = GFR9He2SUE5K…`. The chunk for `X` has the
same grammar: six `0x26` app tags in pre-order, then `0x25 0x31 ref(HAdd.hAdd)`
followed by its three universe levels (`03 00…` then `10 10 10`, three
`zero`s), the three `Nat`s, the sub-chunk for `instHAdd Nat instAddNat`,
the bound variable `0x21` with index `0`, and the `OfNat.ofNat` subterm
with the literal `0` as `0x2A` followed by a zero-length big-endian
integer. Its id is `GDCjqMMoTNkX…`. Climbing back up:

| subterm | id |
|---|---|
| `bvar 0` | `8LnFeTLCRnbF…` |
| `Eq Nat` | `GJkAaqyBNP1s…` |
| `X` | `GDCjqMMoTNkX…` |
| `(Eq Nat) X` | `79J7BZ9VcMpE…` |
| `(Eq Nat X) n` | `HEAk1J7KQnaT…` |
| the whole type | `FRtpGERwGjSX…` |

The last line is `SHA-256(0x28 ‖ 0x00 ‖ id(Nat) ‖ id(body))`: forall tag,
default binder, the two child ids. Binder *names* never appear;
binder *info* does.

A caution about the intermediate rows: they are ids of de Bruijn
*fragments*, meaningful only inside this closed term. `id(bvar 0)` is the
id of "the innermost bound variable", whatever it denotes, and `id(body)`
would differ for the same body placed under one more binder. They are
what the library memoises, within and across declarations, and they are
sound for that. Only the root — a closed term — is an address. Hashing
open fragments modulo α is the problem of
[Hashing Modulo Alpha-Equivalence](https://simon.peytonjones.org/assets/pdfs/hashing-modulo-alpha.pdf)
(PLDI 2021), which CA does not attempt.

## 5. The statement id

```
stmt = SHA-256( 0xA1 ‖ 0x01 ‖ 00 00 00 00 00 00 00 00 ‖ id(type) )
                 STMT   scheme   #levelParams = 0        FRtpGERw…
     = ByKFv4nqHrcsFWuBFd7ihUXKFNEdMvFdMvjW7n8XE3nn
```

Because `Nat.add_zero` is a theorem, `ref = stmt`. Its `decl`, which
does include the proof, exists but nothing downstream ever embeds it.

## 6. Why the right-hand panel holds

A theorem `conj_literal : ∀ n : Nat, n + 0 = n` in any other project
elaborates to the same term, resolves the same seven constants to the
same `ref`s (they are `Init`'s, computed from the same bytes), and runs
the same steps, so it reaches `ByKFv4nqHrcs…`. Its name, its file, its
project and its proof had no byte in any preimage. What *would* change
the id: a different statement; redefining any of the 31 constants in the
cone, including a Lean release that recompiles `Nat.add`; or a bump of
the encoding scheme, which is why the scheme byte is in the preimage.

The coarse `type_hash` of the same statement is the SHA-256 of a
different serialisation, 250 bytes starting `08 00 05 03 00…`: forall
tag, binder info, const tag, and then the *name* `Nat` as a
length-prefixed string. It is `d73f3967fc94…` and it survives a Lean
release, at the price of not noticing if `instAddNat` changed.

## 7. Reproduce it

```lean
import CA
open Lean CA.RefHash CA.SHA256

#eval show Elab.Command.CommandElabM Unit from do
  let env ← getEnv
  let some ci := env.find? `Nat.add_zero | throwError "?"
  let cone := CA.Registry.statementCone env #[`Nat.add_zero]
  let (ids, table) ← computeIds cone {} pureHasher (withProofs := false)
  let resolve (m : Name) : RefEnc :=
    match table.get? m with | some r => .id r | none => .byName m
  let ty := CA.Canonical.canonicalizeL0Decl ci.levelParams ci.type
  let (idTy, _) ← (exprId resolve ty).run {}
  let stmt := sha256Pure ((((ByteArray.empty.push 0xA1).push 0x01) ++ ByteArray.mk #[0,0,0,0,0,0,0,0]) ++ idTy)
  let d := ids.find? (·.name == `Nat.add_zero) |>.get!
  logInfo m!"cone {cone.size}; id(type) {toB58 idTy}; stmt {toB58 stmt}; library says {toB58 d.stmt}"
```

Content-addressed identity for Lean 4 declarations: a SHA-256 address
derived from what a declaration *is* — its elaborated type and value,
with everything it references addressed the same way — rather than from
the name, file or project it happens to live in.

Two declarations with different names but identical mathematical
content receive the same address. A declaration whose statement quietly
changes — because a constant it mentions was redefined — does not.

## Keeping this page true

The `Init` refs, the subterm ids and the final `stmt` are specific to
the toolchain and the encoding scheme. When either changes, rerun the
`#eval` above and `docs/banner.py`, and update the tables here together
with the banner.

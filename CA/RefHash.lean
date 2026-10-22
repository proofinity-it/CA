import Lean
import CA.Base58
import CA.Canonical
import CA.SHA256
import CA.Util

/-!
# CA.RefHash — content identity for declarations (`stmt` / `decl` / `ref`)

The L0 hash (`CA.Canonical.canonicalizeL0` + `CA.ExprHash.serializeExpr`)
identifies a *statement* up to universe renaming — but it keeps constant
**names** inside the expression, so `theorem t : IsSolvable G` hashes the
same in two libraries whose `IsSolvable` differ, and it hashes the *type*
only, so every `inductive Foo : Type` and every definition of type
`∀ (G : Type u) [Group G], Prop` collide. Both are wrong for a
decentralized registry, where a name is exactly the thing two publishers
do not coordinate on and a definition *is* its value.

This module computes three ids per constant `c`, by mutual recursion over
the reference DAG (foundations first):

```
ref(c)  = stmt(c)                    if c is a theorem   (proof irrelevance:
                                     dependents cannot observe the proof)
        = decl(c)                    otherwise           (value is meaning)

stmt(c) = H( STMT ‖ v ‖ #levelParams ‖ ⟦type c⟧ )
decl(c) = H( DECL ‖ v ‖ kind ‖ flags ‖ stmt(c) ‖ ⟦value c⟧? ‖ structural fields )
```

where `v` is the encoding-scheme version byte (`CA.schemeVersion`) and
`⟦e⟧` is the **Merkle id** of the L0-canonical expression `e`
(universes renamed *positionally* from the declaration's `levelParams`
binder list — use sites instantiate levels positionally, so binder order
is part of the identity while binder names are not; universe levels
normalised, so definitionally equal levels agree; `mdata` stripped;
`Nat` literals encoded at full precision):
each node hashes to `H(tag ‖ scalars ‖ ids of children)`, and a
`.const r` node embeds `ref(r)` — never the name. Merkle hashing (per node, memoised
on structurally-equal subterms) is what makes this tractable on `decide`
proofs whose *tree* has 10⁸ nodes but whose DAG is small; the flat
serialisation used by `ExprHash` expands such DAGs into trees.

**Blocks.** Mutual definitions and inductive families (type + ctors +
recursors + nested auxiliaries) reference each other cyclically. Each
strongly connected component of the reference graph is hashed as one
unit: members are put in a canonical order, intra-block references are
encoded as `BLOCKREF ‖ index`, and

```
block   = H( BLOCK ‖ v ‖ n ‖ member₀ ‖ … ‖ memberₙ₋₁ )
decl(mᵢ) = H( MEMBER ‖ v ‖ block ‖ i )
```

so a member's identity is the whole block plus its position, and its
`stmt` is then computed with the sibling `decl`s as references. Names
never enter any of these hashes.

Constants that are referenced but not in the input set (nor in the
caller-supplied `base` table) are hashed **by name** as a fallback and
reported in `DeclIds.unresolved`; callers that need exact ids must
supply a complete base table (e.g. `computeIds` over the whole
environment, foundations first).

Hashing goes through a `CA.SHA256.Hasher` (default: the pure-Lean
`sha256Pure`; the `ca` CLI passes an OpenSSL-backed one). Ids do not
depend on which is used.
-/

open Lean
open CA.Canonical
open CA.SHA256
open CA.Util

namespace CA.RefHash

/-! ## Encoding helpers -/

private def pushU8 (b : ByteArray) (x : UInt8) : ByteArray := b.push x

private def pushU64 (b : ByteArray) (n : UInt64) : ByteArray := Id.run do
  let mut b := b
  let mut v := n
  for _ in [:8] do
    b := b.push (v &&& 0xFF).toUInt8
    v := v >>> 8
  return b

private def pushNat (b : ByteArray) (n : Nat) : ByteArray := pushU64 b n.toUInt64

private def pushBytes (b : ByteArray) (bs : ByteArray) : ByteArray :=
  (pushNat b bs.size) ++ bs

private def pushString (b : ByteArray) (s : String) : ByteArray :=
  pushBytes b s.toUTF8

private def pushName (b : ByteArray) (n : Name) : ByteArray :=
  pushString b n.toString

/-- Arbitrary-precision `Nat` (for literals): length-prefixed minimal
    big-endian bytes. `pushNat` truncates to 64 bits, which made every
    literal `≥ 2^64` collide with its residue (scheme 0). -/
private def pushNatBig (b : ByteArray) (n : Nat) : ByteArray :=
  pushBytes b (natToBytesBE n)

/-- The encoding-scheme version byte mixed into every top-level preimage
    (`STMT`, `DECL`, `BLOCK`, `MEMBER`), right after the domain tag. See
    `CA.schemeVersion`. -/
def schemeVersion : UInt8 := CA.schemeVersion.toUInt8

private def pushBinderInfo (b : ByteArray) : BinderInfo → ByteArray
  | .default        => b.push 0
  | .implicit       => b.push 1
  | .strictImplicit => b.push 2
  | .instImplicit   => b.push 3

private partial def pushLevel (b : ByteArray) (l : Level) : ByteArray :=
  match l with
  | .zero       => pushU8 b 0x10
  | .succ l     => pushLevel (pushU8 b 0x11) l
  | .max l1 l2  => pushLevel (pushLevel (pushU8 b 0x12) l1) l2
  | .imax l1 l2 => pushLevel (pushLevel (pushU8 b 0x13) l1) l2
  | .param n    => pushName (pushU8 b 0x14) n
  | .mvar id    => pushName (pushU8 b 0x15) id.name

/-- Domain-separation tags for the top-level hashes. -/
private def tagStmt   : UInt8 := 0xA1
private def tagDecl   : UInt8 := 0xA2
private def tagBlock  : UInt8 := 0xA3
private def tagMember : UInt8 := 0xA4

/-- Node tags (disjoint from `ExprHash.serializeExpr`'s so the two schemes
    can never produce equal preimages by accident). -/
private def nBVar    : UInt8 := 0x21
private def nFVar    : UInt8 := 0x22
private def nMVar    : UInt8 := 0x23
private def nSort    : UInt8 := 0x24
private def nConst   : UInt8 := 0x25
private def nApp     : UInt8 := 0x26
private def nLam     : UInt8 := 0x27
private def nForall  : UInt8 := 0x28
private def nLet     : UInt8 := 0x29
private def nLitNat  : UInt8 := 0x2A
private def nLitStr  : UInt8 := 0x2B
private def nProj    : UInt8 := 0x2C

/-- How a constant reference is embedded in an encoding. -/
inductive RefEnc where
  /-- A resolved 32-byte `ref` id. -/
  | id (bytes : ByteArray)
  /-- Reference to member `i` of the block currently being hashed. -/
  | blockLocal (i : Nat)
  /-- Not resolvable: fall back to the name (reported as unresolved). -/
  | byName (n : Name)

private def pushRefEnc (b : ByteArray) : RefEnc → ByteArray
  | .id bytes    => (pushU8 b 0x31) ++ bytes
  | .blockLocal i => pushNat (pushU8 b 0x32) i
  | .byName n    => pushName (pushU8 b 0x33) n

/-- Lexicographic comparison of two byte arrays. -/
private def bytesCmp (a b : ByteArray) : Ordering := Id.run do
  let n := Nat.min a.size b.size
  for i in [:n] do
    let x := a.get! i
    let y := b.get! i
    if x < y then return .lt
    if x > y then return .gt
  if a.size < b.size then return .lt
  if a.size > b.size then return .gt
  return .eq

/-! ## Merkle hashing of expressions -/

/-- Memo shared across declarations. Valid only for subterms hashed under
    a *stable* resolver (every constant → its final `ref`), i.e. never for
    block-local encodings, and never for subterms that contained a
    by-name fallback (the name might resolve later and the cached id
    would then be stale). Capped: cleared when it grows past `sharedMemoCap`
    entries. -/
abbrev SharedMemo := IO.Ref (Std.HashMap ExprStructEq ByteArray)

private def sharedMemoCap : Nat := 2000000

/-- Per-computation state: the per-declaration memo of subterm ids (with a
    flag marking subterms whose hash involved a by-name fallback), the
    optional shared memo, and the names that had to be hashed by name. -/
structure HashCtx where
  memo       : Std.HashMap ExprStructEq (ByteArray × Bool) := {}
  shared     : Option SharedMemo := none
  unresolved : NameSet := {}
  /-- SHA-256 implementation (`pureHasher` by default; the CLI plugs in
      OpenSSL). Digests are identical whichever is used. -/
  hasher     : Hasher := pureHasher
  /-- Hash theorem proofs? `false` makes `decl` of a theorem the
      statement-only `H(DECL ‖ v ‖ kind ‖ stmt)`; `stmt` and `ref` are
      unaffected (`ref(theorem) = stmt`). See `computeIds`. -/
  withProofs : Bool := true
  /-- Number of by-name fallbacks seen so far (to decide whether a
      subterm is safe to put in the shared memo). -/
  fallbacks  : Nat := 0

abbrev HashM := StateRefT HashCtx IO

private def sha (b : ByteArray) : HashM ByteArray := do (← get).hasher b

/-- Subterms up to this `approxDepth` are hashed *flat* (one SHA-256 over
    their whole serialisation) instead of node by node. A depth-limited
    subtree is small (≤ 2^d nodes), so the flat encoding is bounded, and
    it removes the per-node FFI call that dominates on typical terms.
    Deeper terms are combined Merkle-style from their children, which is
    what keeps `decide`-style DAGs linear. -/
private def flatDepth : UInt32 := 6

/-- Flat encoding of a shallow expression (references through `resolve`,
    unresolved names noted). Same node tags as the Merkle path so the two
    encodings never collide: a flat chunk is wrapped in `nFlat`. -/
private partial def flatEncode (resolve : Name → RefEnc) (e : Expr) (buf : ByteArray) : HashM ByteArray := do
  match e with
  | .bvar n => return pushNat (pushU8 buf nBVar) n
  | .fvar id => return pushName (pushU8 buf nFVar) id.name
  | .mvar id => return pushName (pushU8 buf nMVar) id.name
  | .sort l => return pushLevel (pushU8 buf nSort) l
  | .const name levels =>
    let r := resolve name
    if let .byName n := r then
      modify fun s => { s with unresolved := s.unresolved.insert n, fallbacks := s.fallbacks + 1 }
    let b := pushRefEnc (pushU8 buf nConst) r
    return levels.foldl pushLevel (pushNat b levels.length)
  | .app f a =>
    let b ← flatEncode resolve f (pushU8 buf nApp)
    flatEncode resolve a b
  | .lam _ t body bi =>
    let b ← flatEncode resolve t (pushBinderInfo (pushU8 buf nLam) bi)
    flatEncode resolve body b
  | .forallE _ t body bi =>
    let b ← flatEncode resolve t (pushBinderInfo (pushU8 buf nForall) bi)
    flatEncode resolve body b
  | .letE _ t v body _ =>
    let b ← flatEncode resolve t (pushU8 buf nLet)
    let b ← flatEncode resolve v b
    flatEncode resolve body b
  | .lit (.natVal n) => return pushNatBig (pushU8 buf nLitNat) n
  | .lit (.strVal s) => return pushString (pushU8 buf nLitStr) s
  | .mdata _ e' => flatEncode resolve e' buf
  | .proj typeName idx s =>
    let r := resolve typeName
    if let .byName n := r then
      modify fun st => { st with unresolved := st.unresolved.insert n, fallbacks := st.fallbacks + 1 }
    flatEncode resolve s (pushNat (pushRefEnc (pushU8 buf nProj) r) idx)

private def nFlat : UInt8 := 0x2F

/-- Merkle id of an (already L0-canonical) expression under a reference
    resolver. `resolve` maps a constant name to how it is embedded. -/
partial def exprId (resolve : Name → RefEnc) (e : Expr) : HashM ByteArray := do
  let key : ExprStructEq := ⟨e⟩
  if let some (h, dirty) := (← get).memo.get? key then
    -- A memo hit must re-surface the subterm's fallback status: an
    -- enclosing window that only sees the cached id would otherwise
    -- believe the subterm clean and publish itself to the shared memo
    -- (and a *shared* hit downstream would then under-report
    -- `unresolved`, breaking "empty means exact").
    if dirty then modify fun s => { s with fallbacks := s.fallbacks + 1 }
    return h
  if let some sm := (← get).shared then
    -- Shared entries are published only when clean, so no flag needed.
    if let some h := (← sm.get).get? key then return h
  let noteRef (r : RefEnc) : HashM Unit := do
    if let .byName n := r then
      modify fun s => { s with unresolved := s.unresolved.insert n, fallbacks := s.fallbacks + 1 }
  let fallbacksBefore := (← get).fallbacks
  let h ← if e.approxDepth ≤ flatDepth then
      sha (← flatEncode resolve e (pushU8 .empty nFlat))
    else match e with
    | .bvar n => sha (pushNat (pushU8 .empty nBVar) n)
    | .fvar id => sha (pushName (pushU8 .empty nFVar) id.name)
    | .mvar id => sha (pushName (pushU8 .empty nMVar) id.name)
    | .sort l => sha (pushLevel (pushU8 .empty nSort) l)
    | .const name levels =>
      let r := resolve name
      noteRef r
      let b := pushRefEnc (pushU8 .empty nConst) r
      let b := levels.foldl pushLevel (pushNat b levels.length)
      sha b
    | .app f a =>
      let hf ← exprId resolve f
      let ha ← exprId resolve a
      sha ((pushU8 .empty nApp) ++ hf ++ ha)
    | .lam _ t body bi =>
      let ht ← exprId resolve t
      let hb ← exprId resolve body
      sha ((pushBinderInfo (pushU8 .empty nLam) bi) ++ ht ++ hb)
    | .forallE _ t body bi =>
      let ht ← exprId resolve t
      let hb ← exprId resolve body
      sha ((pushBinderInfo (pushU8 .empty nForall) bi) ++ ht ++ hb)
    | .letE _ t v body _ =>
      let ht ← exprId resolve t
      let hv ← exprId resolve v
      let hb ← exprId resolve body
      sha ((pushU8 .empty nLet) ++ ht ++ hv ++ hb)
    | .lit (.natVal n) => sha (pushNatBig (pushU8 .empty nLitNat) n)
    | .lit (.strVal s) => sha (pushString (pushU8 .empty nLitStr) s)
    | .mdata _ e' => exprId resolve e'
    | .proj typeName idx s =>
      let r := resolve typeName
      noteRef r
      let hs ← exprId resolve s
      sha ((pushNat (pushRefEnc (pushU8 .empty nProj) r) idx) ++ hs)
  let dirty := (← get).fallbacks != fallbacksBefore
  modify fun st => { st with memo := st.memo.insert key (h, dirty) }
  -- Publish to the shared memo when this subterm involved no by-name
  -- fallback anywhere below it (its id is final) — leaves and constants
  -- included, since those are exactly the entries that repeat across
  -- declarations.
  if !dirty then
    if let some sm := (← get).shared then
      sm.modify fun m => (if m.size > sharedMemoCap then {} else m).insert key h
  return h

/-! ## Per-declaration encodings -/

private def kindTag : ConstantInfo → UInt8
  | .axiomInfo _  => 1
  | .defnInfo _   => 2
  | .thmInfo _    => 3
  | .opaqueInfo _ => 4
  | .quotInfo _   => 5
  | .inductInfo _ => 6
  | .ctorInfo _   => 7
  | .recInfo _    => 8

private def safetyTag : DefinitionSafety → UInt8
  | .safe => 0 | .unsafe => 1 | .partial => 2

private def quotKindTag : QuotKind → UInt8
  | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3

/-- Is this constant *proof-irrelevant to its dependents*? Only theorems:
    the kernel never needs a theorem's value to check a user. (Axioms have
    no value; `opaque`s are kept value-inclusive — conservative for a build
    system, since a changed opaque body changes compiled code even though
    no type-checker can tell.) -/
def isProofIrrelevant : ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

/-- The constants a declaration references, including the structural
    references that live outside `Expr`s (mutual block, constructors,
    inductive of a constructor, recursor rules). Mirrors
    `declbuild`'s `EnvAssembly.constantsOf`. -/
def refsOf (ci : ConstantInfo) (withProofs : Bool := true) : NameSet := Id.run do
  let ins (acc : NameSet) (ns : List Name) : NameSet :=
    ns.foldl (fun (a : NameSet) n => a.insert n) acc
  let acc : NameSet := collectConstants ci.type
  -- `ConstantInfo.value?` is `some` for definitions and theorems only;
  -- an `opaque`'s body is a value too (its own kernel check needs it).
  -- With `withProofs := false` a theorem's proof is not a reference:
  -- nothing a dependent can observe lives in it.
  let acc : NameSet := match ci with
    | .defnInfo v   => collectConstants v.value acc
    | .thmInfo v    => if withProofs then collectConstants v.value acc else acc
    | .opaqueInfo v => collectConstants v.value acc
    | _ => acc
  -- `v.all` lists the declarations of the surrounding mutual block —
  -- including the declaration itself, for *every* def/theorem/opaque/
  -- inductive. The self-entry must be dropped: keeping it made every
  -- ordinary declaration a self-loop SCC, so everything took the block
  -- path (`decl = H(MEMBER ‖ block ‖ 0)`), the documented standalone
  -- encoding was dead code, and the block passes bypassed the shared
  -- memo. Genuine self-references (e.g. `foo._unsafe_rec` calling
  -- itself) live in the *value* and are kept by `collectConstants` —
  -- those singletons still form self-loop SCCs, as intended.
  let notSelf (ns : List Name) : List Name := ns.filter (· != ci.name)
  let acc : NameSet := match ci with
    | .inductInfo v => ins acc (v.ctors ++ notSelf v.all)
    | .ctorInfo v   => acc.insert v.induct
    | .recInfo v    =>
      v.rules.foldl (fun (a : NameSet) r => collectConstants r.rhs (a.insert r.ctor)) (ins acc v.all)
    | .defnInfo v   => ins acc (notSelf v.all)
    | .opaqueInfo v => ins acc (notSelf v.all)
    | .thmInfo v    => ins acc (notSelf v.all)
    | _ => acc
  return acc

/-- Statement encoding of an expression `ty` under universe binders
    `levelParams`: `STMT ‖ v ‖ #levelParams ‖ ⟦ty⟧`. -/
private def stmtHashCore (resolve : Name → RefEnc) (levelParams : List Name) (ty : Expr) :
    HashM ByteArray := do
  let ht ← exprId resolve (canonicalizeL0Decl levelParams ty)
  sha ((pushNat (pushU8 (pushU8 .empty tagStmt) schemeVersion) levelParams.length) ++ ht)

/-- Statement encoding of a declaration: its type under its binders. -/
private def stmtHash (resolve : Name → RefEnc) (ci : ConstantInfo) : HashM ByteArray :=
  stmtHashCore resolve ci.levelParams ci.type

/-- The kind-specific tail of the declaration encoding: value (if any)
    and structural fields, with constant references through `resolve`. -/
private def declTail (resolve : Name → RefEnc) (ci : ConstantInfo) : HashM ByteArray := do
  let refBytes (n : Name) : ByteArray :=
    pushRefEnc .empty (resolve n)
  match ci with
  | .axiomInfo v =>
    return pushU8 .empty (if v.isUnsafe then 1 else 0)
  | .defnInfo v =>
    let hv ← exprId resolve (canonicalizeL0Decl v.levelParams v.value)
    return (pushU8 .empty (safetyTag v.safety)) ++ hv
  | .thmInfo v =>
    if (← get).withProofs then
      exprId resolve (canonicalizeL0Decl v.levelParams v.value)
    else
      return .empty
  | .opaqueInfo v =>
    let hv ← exprId resolve (canonicalizeL0Decl v.levelParams v.value)
    return (pushU8 .empty (if v.isUnsafe then 1 else 0)) ++ hv
  | .quotInfo v =>
    return pushU8 .empty (quotKindTag v.kind)
  | .inductInfo v =>
    let mut b := pushNat (pushNat .empty v.numParams) v.numIndices
    b := pushNat b v.numNested
    b := pushU8 b (if v.isRec then 1 else 0)
    b := pushU8 b (if v.isUnsafe then 1 else 0)
    b := pushU8 b (if v.isReflexive then 1 else 0)
    b := pushNat b v.ctors.length
    for c in v.ctors do b := b ++ refBytes c
    return b
  | .ctorInfo v =>
    let mut b := refBytes v.induct
    b := pushNat b v.cidx
    b := pushNat b v.numParams
    b := pushNat b v.numFields
    b := pushU8 b (if v.isUnsafe then 1 else 0)
    return b
  | .recInfo v =>
    let mut b := pushNat (pushNat .empty v.numParams) v.numIndices
    b := pushNat b v.numMotives
    b := pushNat b v.numMinors
    b := pushU8 b (if v.k then 1 else 0)
    b := pushU8 b (if v.isUnsafe then 1 else 0)
    b := pushNat b v.rules.length
    for r in v.rules do
      b := b ++ refBytes r.ctor
      b := pushNat b r.nfields
      b := b ++ (← exprId resolve (canonicalizeL0Decl v.levelParams r.rhs))
    return b

/-- Full member encoding used inside a block hash and for standalone
    declarations: `kind ‖ stmt-part ‖ tail`. -/
private def memberEncoding (resolve : Name → RefEnc) (ci : ConstantInfo) : HashM ByteArray := do
  let hs ← stmtHash resolve ci
  let tail ← declTail resolve ci
  return (pushU8 .empty (kindTag ci)) ++ hs ++ tail

/-! ## Results -/

/-- The ids of one declaration. All byte arrays are 32-byte SHA-256 digests. -/
structure DeclIds where
  name : Name
  /-- Statement id (type, references by `ref`; universe arity). -/
  stmt : ByteArray
  /-- Declaration id (kind, statement, value, structural fields). -/
  decl : ByteArray
  /-- What dependents embed: `stmt` for theorems, `decl` otherwise. -/
  ref  : ByteArray
  /-- `(blockId, index)` when the declaration is a member of a mutual /
      inductive block of size > 1 (or a self-referential singleton). -/
  block : Option (ByteArray × Nat) := none
  /-- Constants that had to be hashed by name because no id was
      available for them. Empty means the ids are exact. -/
  unresolved : Array Name := #[]
  deriving Inhabited

/-- `name ↦ ref` for constants whose ids are already known. -/
abbrev RefTable := Std.HashMap Name ByteArray

/-! ## Strongly connected components (Tarjan, iterative) -/

/-- SCCs of the graph `succ` over `nodes`, in dependency-first order (an
    SCC appears after every SCC it has an edge into). Edges to nodes
    outside `nodes` are ignored. Iterative Tarjan (deep proof-term
    dependency chains would overflow the stack recursively). -/
def sccs (nodes : Array Name) (succ : Name → Array Name) : Array (Array Name) := Id.run do
  let inSet : NameSet := nodes.foldl (·.insert ·) {}
  -- Successor lists are computed once per node: `succ` may walk a whole
  -- proof term (`refsOf`), and the iterative traversal below revisits a
  -- node once per successor.
  let mut succCache : Std.HashMap Name (Array Name) := {}
  for n in nodes do
    succCache := succCache.insert n ((succ n).filter inSet.contains)
  let mut index : Std.HashMap Name Nat := {}
  let mut low   : Std.HashMap Name Nat := {}
  let mut onStack : NameSet := {}
  let mut stack : Array Name := #[]
  let mut counter : Nat := 0
  let mut out : Array (Array Name) := #[]
  for root in nodes do
    if index.contains root then continue
    -- Explicit call stack of (node, next successor position).
    let mut call : Array (Name × Nat) := #[(root, 0)]
    index := index.insert root counter
    low := low.insert root counter
    counter := counter + 1
    stack := stack.push root
    onStack := onStack.insert root
    while !call.isEmpty do
      let (v, pos) := call.back!
      let vs := succCache.getD v #[]
      if pos < vs.size then
        call := call.pop.push (v, pos + 1)
        let w := vs[pos]!
        if !index.contains w then
          index := index.insert w counter
          low := low.insert w counter
          counter := counter + 1
          stack := stack.push w
          onStack := onStack.insert w
          call := call.push (w, 0)
        else if onStack.contains w then
          low := low.insert v (Nat.min (low.getD v 0) (index.getD w 0))
      else
        -- v finished: propagate lowlink to parent, pop an SCC if root.
        call := call.pop
        if let some (p, _) := call.back? then
          low := low.insert p (Nat.min (low.getD p 0) (low.getD v 0))
        if low.getD v 0 == index.getD v 0 then
          let mut comp : Array Name := #[]
          let mut go := true
          while go do
            let w := stack.back!
            stack := stack.pop
            onStack := onStack.erase w
            comp := comp.push w
            if w == v then go := false
          out := out.push comp
  return out

/-! ## Main entry point -/

/-- Compute `stmt` / `decl` / `ref` for every declaration in `decls`.
    Dependencies among the input are ordered automatically (SCCs,
    foundations first). References to constants outside the input are
    resolved through `base`; anything found in neither is hashed by name
    and reported in `unresolved`.

    Returns the ids in the input order and the extended `RefTable`
    (`base` plus every input declaration's `ref`).

    `withProofs := false` leaves theorem proofs out: they are neither
    hashed nor followed as references. `stmt` and `ref` of every
    declaration are unchanged (a theorem's `ref` is its `stmt`), while a
    theorem's `decl` becomes the statement-only `H(DECL ‖ v ‖ kind ‖ stmt)`.
    This is the mode for computing the ids a *registry* or a *dependent*
    needs, where no proof term is ever observable, and it makes the
    required cone of an environment far smaller. -/
def computeIds (decls : Array (Name × ConstantInfo)) (base : RefTable := {})
    (hasher : Hasher := pureHasher) (withProofs : Bool := true) : IO (Array DeclIds × RefTable) := do
  let declMap : Std.HashMap Name ConstantInfo :=
    decls.foldl (fun m (n, ci) => m.insert n ci) {}
  let names := decls.map (·.1)
  let refsCache : Std.HashMap Name (Array Name) :=
    decls.foldl (fun m (n, ci) => m.insert n (refsOf ci withProofs).toArray) {}
  let succ (n : Name) : Array Name := refsCache.getD n #[]
  let comps := sccs names succ
  -- `table` is a plain local: every closure that captures it must be
  -- dead before it is mutated, or the insert copies the whole map (an
  -- `IO.Ref` shared with a live local had exactly that effect: one full
  -- copy per block member — quadratic on Mathlib).
  let mut table : RefTable := base
  let shared : SharedMemo ← IO.mkRef {}
  let mut results : Std.HashMap Name DeclIds := {}
  -- Optional trace (`CA_REFHASH_TRACE=1`): progress every 20k components
  -- and every component that takes more than a second, on stderr.
  let trace := (← IO.getEnv "CA_REFHASH_TRACE").isSome
  let tStart ← IO.monoMsNow
  let mut done : Nat := 0
  let mut slowest : Nat := 0
  if trace then
    IO.eprintln s!"refhash: {decls.size} decls, {comps.size} components (sccs {(← IO.monoMsNow) - tStart} ms)"

  for comp in comps do
    let tComp ← IO.monoMsNow
    let selfLoop := comp.size == 1 && (succ comp[0]!).contains comp[0]!
    if comp.size == 1 && !selfLoop then
      -- Standalone declaration.
      let n := comp[0]!
      let some ci := declMap.get? n | continue
      let resolve (m : Name) : RefEnc :=
        match table.get? m with
        | some r => .id r
        | none => .byName m
      let (ids, st) ← (do
          let s ← stmtHash resolve ci
          let tail ← declTail resolve ci
          let d ← (sha ((pushU8 (pushU8 .empty tagDecl) schemeVersion) ++ (pushU8 .empty (kindTag ci)) ++ s ++ tail) : HashM ByteArray)
          let r := if isProofIrrelevant ci then s else d
          pure (s, d, r)) |>.run { shared := some shared, hasher, withProofs }
      let (s, d, r) := ids
      results := results.insert n {
        name := n, stmt := s, decl := d, ref := r,
        unresolved := st.unresolved.toArray }
      table := table.insert n r
    else
      -- Block: canonical member order, then block hash, then member ids.
      -- Shape hash: member encoding with intra-block references made
      -- anonymous. Ties (structurally identical members) are broken by
      -- the position in the anchor's `all` / constructor index, so the
      -- assignment name → member index is stable for a given source.
      let inBlock : NameSet := comp.foldl (·.insert ·) {}
      let anonResolve (m : Name) : RefEnc :=
        if inBlock.contains m then .blockLocal 0
        else match table.get? m with
          | some r => .id r
          | none => .byName m
      let mut shaped : Array (ByteArray × Nat × Name) := #[]
      -- Source-order key: `all`-position × 1000 + cidx, best effort.
      let srcKey (n : Name) : Nat :=
        match declMap.get? n with
        | some (.ctorInfo v) =>
          let allL := match declMap.get? v.induct with
            | some (.inductInfo iv) => iv.all
            | _ => []
          (allL.idxOf v.induct) * 1000 + v.cidx + 1
        | some (.inductInfo v) => (v.all.idxOf n) * 1000
        | some (.recInfo v) => (v.all.length) * 1000 + 900 + (v.all.idxOf (n.getPrefix))
        | some (.defnInfo v) => v.all.idxOf n
        | some (.opaqueInfo v) => v.all.idxOf n
        | some (.thmInfo v) => v.all.idxOf n
        | _ => 0
      for n in comp do
        let some ci := declMap.get? n | continue
        let (enc, _) ← (memberEncoding anonResolve ci).run { hasher, withProofs }
        let h ← hasher enc
        shaped := shaped.push (h, srcKey n, n)
      let ordered := shaped.qsort fun (ha, ka, _) (hb, kb, _) =>
        match bytesCmp ha hb with
        | .lt => true
        | .gt => false
        | .eq => ka < kb
      let members := ordered.map (·.2.2)
      let posOf : Std.HashMap Name Nat := Id.run do
        let mut m : Std.HashMap Name Nat := {}
        for i in [:members.size] do
          m := m.insert members[i]! i
        return m
      let localResolve (m : Name) : RefEnc :=
        match posOf.get? m with
        | some i => .blockLocal i
        | none => match table.get? m with
          | some r => .id r
          | none => .byName m
      -- Block hash: encodings collected, concatenated once (appending
      -- to a growing buffer per member is quadratic in the block size).
      let mut encs : Array ByteArray := #[]
      let mut unresolvedAll : NameSet := {}
      for n in members do
        let some ci := declMap.get? n | continue
        let (enc, st) ← (memberEncoding localResolve ci).run { hasher, withProofs }
        for u in st.unresolved do
          unresolvedAll := unresolvedAll.insert u
        encs := encs.push enc
      let total := encs.foldl (fun n e => n + e.size) 0
      let mut blockBuf := ByteArray.emptyWithCapacity (total + 16)
      blockBuf := pushNat (pushU8 (pushU8 blockBuf tagBlock) schemeVersion) members.size
      for e in encs do blockBuf := blockBuf ++ e
      let blockId ← hasher blockBuf
      -- Member decl ids; sibling refs resolve through `memberDecl` first,
      -- then the table — no per-block copy of the table.
      let mut memberDecl : Std.HashMap Name ByteArray := {}
      for i in [:members.size] do
        let d ← hasher (pushNat ((pushU8 (pushU8 .empty tagMember) schemeVersion) ++ blockId) i)
        memberDecl := memberDecl.insert members[i]! d
      let fullResolve (m : Name) : RefEnc :=
        match memberDecl.get? m with
        | some d => .id d
        | none => match table.get? m with
          | some r => .id r
          | none => .byName m
      -- Compute every member's ids while the resolver (which holds a
      -- reference to `table`) is alive; insert into the table afterwards.
      let mut newRefs : Array (Name × ByteArray) := #[]
      for i in [:members.size] do
        let n := members[i]!
        let some ci := declMap.get? n | continue
        let (s, _) ← (stmtHash fullResolve ci).run { shared := some shared, hasher, withProofs }
        let d := memberDecl.get! n
        let r := if isProofIrrelevant ci then s else d
        results := results.insert n {
          name := n, stmt := s, decl := d, ref := r,
          block := some (blockId, i),
          unresolved := unresolvedAll.toArray }
        newRefs := newRefs.push (n, r)
      for (n, r) in newRefs do
        table := table.insert n r
    if trace then
      done := done + 1
      let dt := (← IO.monoMsNow) - tComp
      if dt > slowest then slowest := dt
      if dt > 1000 then
        IO.eprintln s!"refhash: slow component {comp[0]!} (size {comp.size}) {dt} ms"
      if done % 20000 == 0 then
        let sm ← shared.get
        IO.eprintln s!"refhash: {done}/{comps.size} components, {((← IO.monoMsNow) - tStart) / 1000} s, shared memo {sm.size}, slowest {slowest} ms"

  let ordered := decls.filterMap fun (n, _) => results.get? n
  return (ordered, table)

/-- Ids for a single declaration whose dependencies are all in `base`
    (the incremental / build-time case). Same as `computeIds #[(n, ci)]`. -/
def idsOf (name : Name) (ci : ConstantInfo) (base : RefTable)
    (hasher : Hasher := pureHasher) : IO DeclIds := do
  let (r, _) ← computeIds #[(name, ci)] base hasher
  return r[0]!

/-- Statement id of a bare expression `e` under universe binders
    `levelParams`, as if `e` were the type of a theorem:
    `H(STMT ‖ v ‖ #levelParams ‖ ⟦e⟧)`, references resolved through
    `table` (anything missing is hashed by name and reported). This is
    the statement id of an `@[open_point]` `def P : Prop := S`: a
    theorem `: S` gets exactly this `stmt`. -/
def stmtIdOf (levelParams : List Name) (e : Expr) (table : RefTable)
    (hasher : Hasher := pureHasher) : IO (ByteArray × Array Name) := do
  let resolve (m : Name) : RefEnc :=
    match table.get? m with
    | some r => .id r
    | none => .byName m
  let (h, st) ← (stmtHashCore resolve levelParams e).run { hasher }
  return (h, st.unresolved.toArray)

/-- base58btc rendering, so ids print like the existing CA hashes.
    (Alias for `CA.Base58.encode`.) -/
def toB58 (b : ByteArray) : String := CA.Base58.encode b

end CA.RefHash

import Lean
import CA.RefHash

/-!
# CA.Payload — the stored form of a declaration (`docs/payload.md`)

A **unit** holds what the ids read (`docs/spec.md` §4): a standalone
constant, a whole block, or a bare statement, with its canonical terms
(`spec.md` §6) written as one table of nodes in which two subterms equal
up to names are one node. A **decoration** holds what the ids ignore:
the declaration's own name, a name for each reference, universe
parameter names, binder names, reducibility hints, `nonDep` flags. A
**file table** maps the positions units cite to 32-byte `ref` ids and to
names, so each id and name is stored once per file.

Three operations:

* `encodeUnit` / `encodeStatement`: declarations → unit + decorations.
  The encoder decodes its own output and reports whether every member
  comes back exactly (up to level normalisation and `mdata`, which
  canonicalisation removes by definition), so a caller knows when the
  decoration was not enough (`Encoded.exact`).
* `checkUnit`: unit + file refs → ids, recomputed with `CA.RefHash`
  itself over declarations rebuilt with placeholder names. Needs no
  environment and no other unit.
* `decodeUnit` + `rebuild`: unit + decoration + file table →
  `ConstantInfo`s.

This module turns declarations into bytes and back and does nothing else:
no files, no database, no kernel.
-/

open Lean
open CA.RefHash (RefTable DeclIds)

namespace CA.Payload

/-- Payload format version (`p` in `docs/payload.md`), independent of the
    id scheme version. -/
def formatVersion : UInt8 := 1

/-! ## Primitive encodings -/

/-- Unsigned LEB128, minimal. -/
def putUV (b : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut b := b
  let mut n := n
  while n ≥ 0x80 do
    b := b.push (n % 0x80 + 0x80).toUInt8
    n := n / 0x80
  return b.push n.toUInt8

def putBytes (b bs : ByteArray) : ByteArray := putUV b bs.size ++ bs

def putBool (b : ByteArray) (x : Bool) : ByteArray := b.push (if x then 1 else 0)

def putStr (b : ByteArray) (s : String) : ByteArray := putBytes b s.toUTF8

/-- A name, component by component, root first: `uv(#components)`, then
    `0x00 ‖ sv(s)` for a string component and `0x01 ‖ uv(k)` for a
    numeric one. Exact for every `Name`, including hygienic and private
    names, which a dotted rendering cannot round-trip. -/
def putName (b : ByteArray) (n : Name) : ByteArray := Id.run do
  let comps := n.components
  let mut b := putUV b comps.length
  for c in comps do
    match c with
    | .str _ s => b := putStr (b.push 0) s
    | .num _ k => b := putUV (b.push 1) k
    | .anonymous => b := putUV (b.push 1) 0
  return b

abbrev Rd := ReaderT ByteArray (StateT Nat (Except String))

def getU8 : Rd UInt8 := do
  let d ← read
  let p ← get
  if h : p < d.size then
    set (p + 1)
    return d[p]
  else throw s!"truncated at byte {p}"

def getUV : Rd Nat := do
  let mut acc := 0
  let mut shift := 0
  let mut count := 0
  repeat
    let x ← getU8
    count := count + 1
    acc := acc + (x.toNat % 0x80) * 2 ^ shift
    shift := shift + 7
    if x < 0x80 then
      if x == 0 && count > 1 then throw "non-minimal LEB128"
      break
  return acc

def getBytes : Rd ByteArray := do
  let n ← getUV
  let d ← read
  let p ← get
  if p + n > d.size then throw s!"truncated: {n} bytes at {p}"
  set (p + n)
  return d.extract p (p + n)

def getStr : Rd String := do
  match String.fromUTF8? (← getBytes) with
  | some s => return s
  | none => throw "invalid UTF-8"

def getName : Rd Name := do
  let k ← getUV
  let mut n := Name.anonymous
  for _ in [:k] do
    match ← getU8 with
    | 0 => n := .str n (← getStr)
    | 1 => n := .num n (← getUV)
    | t => throw s!"bad name component tag {t}"
  return n

def getBool : Rd Bool := do
  match ← getU8 with
  | 0 => return false
  | 1 => return true
  | t => throw s!"bad boolean {t}"

def Rd.run' (x : Rd α) (d : ByteArray) : Except String α :=
  match (x.run d).run 0 with
  | .ok (a, p) => if p == d.size then .ok a else .error s!"{d.size - p} trailing bytes"
  | .error e => .error e

/-! ## The data model -/

/-- A constant reference inside a unit (`docs/payload.md` §3.1). -/
inductive RRef where
  /-- The member itself; only in a standalone constant's `all`. -/
  | self
  /-- Position `j` in the unit's reference list. -/
  | ref (j : Nat)
  /-- Member `i` of this block. -/
  | member (i : Nat)
  /-- Unresolved: hashed by name (`spec.md` §10). -/
  | byName (n : Name)
  deriving Inhabited, BEq, Hashable

def putRRef (b : ByteArray) : RRef → ByteArray
  | .self => b.push 0x30
  | .ref j => putUV (b.push 0x31) j
  | .member i => putUV (b.push 0x32) i
  | .byName n => putName (b.push 0x33) n

def getRRef : Rd RRef := do
  match ← getU8 with
  | 0x30 => return .self
  | 0x31 => return .ref (← getUV)
  | 0x32 => return .member (← getUV)
  | 0x33 => return .byName (← getName)
  | t => throw s!"bad reference tag {t}"

/-- A level whose parameters are positions (`u_i ↦ i`). -/
inductive PLevel where
  | zero | succ (l : PLevel) | max (a b : PLevel) | imax (a b : PLevel) | param (i : Nat)
  deriving Inhabited, BEq, Hashable

partial def putLevel (b : ByteArray) : PLevel → ByteArray
  | .zero => b.push 0x10
  | .succ l => putLevel (b.push 0x11) l
  | .max x y => putLevel (putLevel (b.push 0x12) x) y
  | .imax x y => putLevel (putLevel (b.push 0x13) x) y
  | .param i => putUV (b.push 0x14) i

partial def getLevel : Rd PLevel := do
  match ← getU8 with
  | 0x10 => return .zero
  | 0x11 => return .succ (← getLevel)
  | 0x12 => let a ← getLevel; let b ← getLevel; return .max a b
  | 0x13 => let a ← getLevel; let b ← getLevel; return .imax a b
  | 0x14 => return .param (← getUV)
  | t => throw s!"bad level tag {t}"

/-- Canonical parameter name `u_i` → `i`. -/
def paramIndex? (n : Name) : Option Nat :=
  match n with
  | .str .anonymous s => if s.startsWith "u_" then (s.drop 2).toNat? else none
  | _ => none

partial def PLevel.ofLevel : Level → Except String PLevel
  | .zero => pure .zero
  | .succ l => return .succ (← ofLevel l)
  | .max a b => return .max (← ofLevel a) (← ofLevel b)
  | .imax a b => return .imax (← ofLevel a) (← ofLevel b)
  | .param n => match paramIndex? n with
    | some i => pure (.param i)
    | none => throw s!"level parameter {n} is not canonical"
  | .mvar _ => throw "level metavariable in a kernel declaration"

partial def PLevel.toLevel (name : Nat → Name) : PLevel → Level
  | .zero => .zero
  | .succ l => .succ (l.toLevel name)
  | .max a b => .max (a.toLevel name) (b.toLevel name)
  | .imax a b => .imax (a.toLevel name) (b.toLevel name)
  | .param i => .param (name i)

/-- One node of a unit's table. Children are absolute node indices here;
    on the wire they are distances back (`docs/payload.md` §3.2). -/
inductive Node where
  | bvar (i : Nat)
  | sort (l : PLevel)
  | const (r : RRef) (ls : List PLevel)
  | app (f a : Nat)
  /-- `slot`: the binder's name slot (one per distinct binder name). -/
  | lam (bi : BinderInfo) (slot : Nat) (t b : Nat)
  | forallE (bi : BinderInfo) (slot : Nat) (t b : Nat)
  | letE (slot : Nat) (nonDep : Bool) (t v b : Nat)
  | natLit (n : Nat)
  | strLit (s : String)
  | proj (r : RRef) (i : Nat) (s : Nat)
  deriving Inhabited, BEq, Hashable

def biByte : BinderInfo → UInt8
  | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3

def biOf : UInt8 → Except String BinderInfo
  | 0 => pure .default | 1 => pure .implicit | 2 => pure .strictImplicit
  | 3 => pure .instImplicit | t => throw s!"bad binder info {t}"

def Node.isBinder : Node → Bool
  | .lam .. | .forallE .. | .letE .. => true
  | _ => false

def putNode (b : ByteArray) (self : Nat) (n : Node) : ByteArray :=
  let back (b : ByteArray) (c : Nat) := putUV b (self - c)
  match n with
  | .bvar i => putUV (b.push 0x21) i
  | .sort l => putLevel (b.push 0x24) l
  | .const r ls => ls.foldl putLevel (putUV (putRRef (b.push 0x25) r) ls.length)
  | .app f a => back (back (b.push 0x26) f) a
  | .lam bi k t body => back (back (putUV ((b.push 0x27).push (biByte bi)) k) t) body
  | .forallE bi k t body => back (back (putUV ((b.push 0x28).push (biByte bi)) k) t) body
  | .letE k nd t v body => back (back (back (putBool (putUV (b.push 0x29) k) nd) t) v) body
  | .natLit n => putBytes (b.push 0x2A) (CA.Util.natToBytesBE n)
  | .strLit s => putStr (b.push 0x2B) s
  | .proj r i s => back (putUV (putRRef (b.push 0x2C) r) i) s

def getNode (self : Nat) : Rd Node := do
  let child : Rd Nat := do
    let d ← getUV
    if d == 0 || d > self then throw s!"node {self}: bad child distance {d}"
    return self - d
  match ← getU8 with
  | 0x21 => return .bvar (← getUV)
  | 0x24 => return .sort (← getLevel)
  | 0x25 =>
    let r ← getRRef
    let k ← getUV
    let mut ls := #[]
    for _ in [:k] do ls := ls.push (← getLevel)
    return .const r ls.toList
  | 0x26 => let f ← child; let a ← child; return .app f a
  | 0x27 =>
    let bi ← match biOf (← getU8) with | .ok b => pure b | .error e => throw e
    let k ← getUV; let t ← child; let b ← child; return .lam bi k t b
  | 0x28 =>
    let bi ← match biOf (← getU8) with | .ok b => pure b | .error e => throw e
    let k ← getUV; let t ← child; let b ← child; return .forallE bi k t b
  | 0x29 =>
    let k ← getUV; let nd ← getBool
    let t ← child; let v ← child; let b ← child; return .letE k nd t v b
  | 0x2A =>
    let bs ← getBytes
    if bs.size > 0 && bs[0]! == 0 then throw "non-minimal natural literal"
    return .natLit (bs.foldl (fun n x => n * 256 + x.toNat) 0)
  | 0x2B => return .strLit (← getStr)
  | 0x2C => let r ← getRRef; let i ← getUV; let s ← child; return .proj r i s
  | t => throw s!"node {self}: bad tag {t}"

/-- Kind-specific fields (`docs/payload.md` §3.3). Terms are node indices. -/
inductive Fields where
  | axiom (isUnsafe : Bool)
  | defn (safety : DefinitionSafety) (value : Nat) (all : Array RRef)
  | thm (value : Option Nat) (all : Array RRef)
  | opaque (isUnsafe : Bool) (value : Nat) (all : Array RRef)
  | quot (kind : QuotKind)
  | induct (numParams numIndices numNested : Nat) (isRec isUnsafe isReflexive : Bool)
      (ctors : Array RRef) (all : Array RRef)
  | ctor (induct : RRef) (cidx numParams numFields : Nat) (isUnsafe : Bool)
  | recursor (numParams numIndices numMotives numMinors : Nat) (k isUnsafe : Bool)
      (rules : Array (RRef × Nat × Nat)) (all : Array RRef)
  deriving Inhabited

structure Member where
  numLevels : Nat
  type : Nat
  fields : Fields
  deriving Inhabited

inductive Form where
  | statement | standalone | block
  deriving Inhabited, BEq, Repr

def Form.byte : Form → UInt8
  | .statement => 0 | .standalone => 1 | .block => 2

structure UnitData where
  form : Form
  /-- Positions in the file's ref table, one per unit reference. -/
  refs : Array Nat
  nodes : Array Node
  /-- `statement`: one member, `fields = .thm none #[]`. -/
  members : Array Member
  deriving Inhabited

def kindByte : Fields → UInt8
  | .axiom .. => 1 | .defn .. => 2 | .thm .. => 3 | .opaque .. => 4
  | .quot .. => 5 | .induct .. => 6 | .ctor .. => 7 | .recursor .. => 8

def safetyByte : DefinitionSafety → UInt8
  | .safe => 0 | .unsafe => 1 | .partial => 2

def quotByte : QuotKind → UInt8
  | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3

def putRRefs (b : ByteArray) (rs : Array RRef) : ByteArray :=
  rs.foldl putRRef (putUV b rs.size)

def putMember (b : ByteArray) (m : Member) : ByteArray :=
  let b := putUV (putUV (b.push (kindByte m.fields)) m.numLevels) m.type
  match m.fields with
  | .axiom u => putBool b u
  | .defn s v all => putRRefs (putUV (b.push (safetyByte s)) v) all
  | .thm v all =>
    let b := match v with | some v => putUV (b.push 1) v | none => b.push 0
    putRRefs b all
  | .opaque u v all => putRRefs (putUV (putBool b u) v) all
  | .quot k => b.push (quotByte k)
  | .induct np ni nn r u refl ctors all =>
    let b := putBool (putBool (putBool (putUV (putUV (putUV b np) ni) nn) r) u) refl
    putRRefs (putRRefs b ctors) all
  | .ctor ind c np nf u => putBool (putUV (putUV (putUV (putRRef b ind) c) np) nf) u
  | .recursor np ni nm nmi k u rules all =>
    let b := putBool (putBool (putUV (putUV (putUV (putUV b np) ni) nm) nmi) k) u
    let b := rules.foldl (fun b (c, nf, rhs) => putUV (putUV (putRRef b c) nf) rhs) (putUV b rules.size)
    putRRefs b all

def getRRefs : Rd (Array RRef) := do
  let k ← getUV
  let mut out := #[]
  for _ in [:k] do out := out.push (← getRRef)
  return out

def getMember : Rd Member := do
  let kind ← getU8
  let numLevels ← getUV
  let type ← getUV
  let fields : Fields ← match kind with
    | 1 => pure (.axiom (← getBool))
    | 2 =>
      let s ← match ← getU8 with
        | 0 => pure DefinitionSafety.safe | 1 => pure .unsafe | 2 => pure .partial
        | t => throw s!"bad safety {t}"
      let v ← getUV
      pure (.defn s v (← getRRefs))
    | 3 =>
      let v ← if ← getBool then some <$> getUV else pure none
      pure (.thm v (← getRRefs))
    | 4 => let u ← getBool; let v ← getUV; pure (.opaque u v (← getRRefs))
    | 5 =>
      let k ← match ← getU8 with
        | 0 => pure QuotKind.type | 1 => pure .ctor | 2 => pure .lift | 3 => pure .ind
        | t => throw s!"bad quotient kind {t}"
      pure (.quot k)
    | 6 =>
      let np ← getUV; let ni ← getUV; let nn ← getUV
      let r ← getBool; let u ← getBool; let refl ← getBool
      let ctors ← getRRefs
      pure (.induct np ni nn r u refl ctors (← getRRefs))
    | 7 =>
      let ind ← getRRef; let c ← getUV; let np ← getUV; let nf ← getUV
      pure (.ctor ind c np nf (← getBool))
    | 8 =>
      let np ← getUV; let ni ← getUV; let nm ← getUV; let nmi ← getUV
      let k ← getBool; let u ← getBool
      let nr ← getUV
      let mut rules := #[]
      for _ in [:nr] do
        let c ← getRRef; let nf ← getUV; let rhs ← getUV
        rules := rules.push (c, nf, rhs)
      pure (.recursor np ni nm nmi k u rules (← getRRefs))
    | t => throw s!"bad kind {t}"
  return { numLevels, type, fields }

/-- Serialise a unit (`docs/payload.md` §3). -/
def UnitData.toBytes (u : UnitData) : ByteArray := Id.run do
  let mut b := (ByteArray.empty.push formatVersion).push u.form.byte
  b := putUV b u.refs.size
  for t in u.refs do b := putUV b t
  b := putUV b u.nodes.size
  for i in [:u.nodes.size] do b := putNode b i u.nodes[i]!
  match u.form with
  | .statement =>
    let m := u.members[0]!
    b := putUV (putUV b m.numLevels) m.type
  | .standalone => b := putMember b u.members[0]!
  | .block =>
    b := putUV b u.members.size
    for m in u.members do b := putMember b m
  return b

def decodeUnit (bytes : ByteArray) : Except String UnitData := Rd.run' (do
  let p ← getU8
  if p != formatVersion then throw s!"payload format {p}, expected {formatVersion}"
  let form ← match ← getU8 with
    | 0 => pure Form.statement | 1 => pure .standalone | 2 => pure .block
    | t => throw s!"bad form {t}"
  let k ← getUV
  let mut refs := #[]
  for _ in [:k] do refs := refs.push (← getUV)
  let m ← getUV
  let mut nodes := #[]
  for i in [:m] do nodes := nodes.push (← getNode i)
  let members ← match form with
    | .statement =>
      let nl ← getUV; let ty ← getUV
      pure #[{ numLevels := nl, type := ty, fields := .thm none #[] : Member }]
    | .standalone => pure #[← getMember]
    | .block =>
      let n ← getUV
      if n < 1 then throw "empty block"
      let mut ms := #[]
      for _ in [:n] do ms := ms.push (← getMember)
      pure ms
  return { form, refs, nodes, members }) bytes

/-! ## File tables -/

/-- The file-level tables units and decorations cite (`docs/payload.md` §6). -/
structure FileTable where
  refs : Array ByteArray := #[]
  refPos : Std.HashMap ByteArray Nat := {}
  names : Array Name := #[]
  namePos : Std.HashMap Name Nat := {}
  deriving Inhabited

def FileTable.refIx (ft : FileTable) (id : ByteArray) : FileTable × Nat :=
  match ft.refPos.get? id with
  | some i => (ft, i)
  | none => ({ ft with refs := ft.refs.push id, refPos := ft.refPos.insert id ft.refs.size }, ft.refs.size)

def FileTable.nameIx (ft : FileTable) (n : Name) : FileTable × Nat :=
  match ft.namePos.get? n with
  | some i => (ft, i)
  | none => ({ ft with names := ft.names.push n, namePos := ft.namePos.insert n ft.names.size }, ft.names.size)

/-! ## Decorations -/

structure Decoration where
  own : Name
  member : Nat
  /-- One file name-table position per unit reference. -/
  refNames : Array Nat
  levelParams : Array Name
  /-- One name per binder slot of the unit. -/
  binders : Array Name
  hints : Option ReducibilityHints := none
  deriving Inhabited

def Decoration.toBytes (d : Decoration) : ByteArray := Id.run do
  let mut b := putUV (putName (ByteArray.empty.push formatVersion) d.own) d.member
  b := putUV b d.refNames.size
  for i in d.refNames do b := putUV b i
  b := putUV b d.levelParams.size
  for p in d.levelParams do b := putName b p
  b := putUV b d.binders.size
  for n in d.binders do b := putName b n
  match d.hints with
  | none => b := b.push 0xFF
  | some .opaque => b := b.push 0
  | some .abbrev => b := b.push 1
  | some (.regular h) => b := putUV (b.push 2) h.toNat
  return b

def decodeDecoration (bytes : ByteArray) : Except String Decoration := Rd.run' (do
  let p ← getU8
  if p != formatVersion then throw s!"payload format {p}, expected {formatVersion}"
  let own ← getName
  let member ← getUV
  let k ← getUV
  let mut refNames := #[]
  for _ in [:k] do refNames := refNames.push (← getUV)
  let nl ← getUV
  let mut levelParams := #[]
  for _ in [:nl] do levelParams := levelParams.push (← getName)
  let nb ← getUV
  let mut binders := #[]
  for _ in [:nb] do binders := binders.push (← getName)
  let hints ← match ← getU8 with
    | 0xFF => pure none
    | 0 => pure (some ReducibilityHints.opaque)
    | 1 => pure (some .abbrev)
    | 2 => pure (some (.regular (← getUV).toUInt32))
    | t => throw s!"bad hints {t}"
  return ⟨own, member, refNames, levelParams, binders, hints⟩) bytes

/-! ## Rebuilding declarations -/

/-- The terms of a unit as `Expr`s, children before parents, sharing kept. -/
def UnitData.exprs (u : UnitData) (constName : RRef → Name) (levelName : Nat → Name)
    (binderName : Nat → Name) : Array Expr := Id.run do
  let mut out : Array Expr := Array.mkEmpty u.nodes.size
  let lv (l : PLevel) := l.toLevel levelName
  for n in u.nodes do
    let e := match n with
      | .bvar i => Expr.bvar i
      | .sort l => .sort (lv l)
      | .const r ls => .const (constName r) (ls.map lv)
      | .app f a => .app out[f]! out[a]!
      | .lam bi k t b => .lam (binderName k) out[t]! out[b]! bi
      | .forallE bi k t b => .forallE (binderName k) out[t]! out[b]! bi
      | .letE k nd t v b => .letE (binderName k) out[t]! out[v]! out[b]! nd
      | .natLit k => .lit (.natVal k)
      | .strLit s => .lit (.strVal s)
      | .proj r i s => .proj (constName r) i out[s]!
    out := out.push e
  return out

/-- Rebuild member `i` as a `ConstantInfo`. `name` names every reference
    (`self` and `member j` included); `levelParams` are the member's
    universe binders; `hints` applies to a definition. -/
def UnitData.constantInfo (u : UnitData) (es : Array Expr) (i : Nat) (name : RRef → Name)
    (levelParams : List Name) (hints : ReducibilityHints := .opaque) : ConstantInfo :=
  let m := u.members[i]!
  let own := name (if u.form == .standalone then .self else .member i)
  let cv : ConstantVal := { name := own, levelParams, type := es[m.type]! }
  let names (rs : Array RRef) : List Name := (rs.map name).toList
  match m.fields with
  | .axiom isUnsafe => .axiomInfo { cv with isUnsafe }
  | .defn safety v all => .defnInfo { cv with value := es[v]!, hints, safety, all := names all }
  | .thm v all =>
    .thmInfo { cv with value := (v.map (es[·]!)).getD (.sort .zero), all := names all }
  | .opaque isUnsafe v all => .opaqueInfo { cv with value := es[v]!, isUnsafe, all := names all }
  | .quot kind => .quotInfo { cv with kind }
  | .induct numParams numIndices numNested isRec isUnsafe isReflexive ctors all =>
    .inductInfo { cv with numParams, numIndices, all := names all, ctors := names ctors,
                          numNested, isRec, isUnsafe, isReflexive }
  | .ctor ind cidx numParams numFields isUnsafe =>
    .ctorInfo { cv with induct := name ind, cidx, numParams, numFields, isUnsafe }
  | .recursor numParams numIndices numMotives numMinors k isUnsafe rules all =>
    .recInfo { cv with all := names all, numParams, numIndices, numMotives, numMinors,
                       rules := (rules.map fun (c, nfields, rhs) =>
                         ({ ctor := name c, nfields, rhs := es[rhs]! } : RecursorRule)).toList,
                       k, isUnsafe }

/-- Rebuild every member of a unit with its decorations (one per member,
    in member order), names from the file table. -/
def rebuild (u : UnitData) (ft : FileTable) (decos : Array Decoration) :
    Except String (Array (Name × ConstantInfo)) := do
  if decos.size != u.members.size then throw "one decoration per member expected"
  let ownOf (i : Nat) := decos[i]!.own
  let d0 := decos[0]!
  let refName (j : Nat) : Name :=
    match d0.refNames[j]? with
    | some p => ft.names[p]?.getD .anonymous
    | none => .anonymous
  let name : RRef → Name
    | .self => d0.own
    | .ref j => refName j
    | .member i => ownOf i
    | .byName n => n
  let mut out := #[]
  for i in [:u.members.size] do
    let d := decos[i]!
    let es := u.exprs name (fun k => d.levelParams[k]?.getD (Name.mkSimple s!"u_{k}"))
      (fun k => d.binders[k]?.getD .anonymous)
    let ci := u.constantInfo es i name d.levelParams.toList (d.hints.getD .opaque)
    out := out.push (d.own, ci)
  return out

/-! ## Checking -/

structure Checked where
  form : Form
  /-- What the unit is filed under: `decl` (standalone), block id, or `stmt`. -/
  key : ByteArray
  /-- `(stmt, decl, ref)` per member, in member order. -/
  ids : Array (ByteArray × ByteArray × ByteArray)
  /-- Names hashed by name (`spec.md` §10): empty means exact. -/
  unresolved : Array Name
  deriving Inhabited

private def refPlaceholder (j : Nat) : Name := .num `_ca_ref j
private def memberPlaceholder (i : Nat) : Name := .num `_ca_member i
private def isPlaceholder (n : Name) : Bool :=
  n.getPrefix == `_ca_ref || n.getPrefix == `_ca_member

/-- Recompute a unit's ids from its bytes and the file's ref table
    (`docs/payload.md` §5). The declarations are rebuilt with placeholder
    names and handed to `CA.RefHash.computeIds`, so the check is the id
    computation itself, not a second implementation of it. -/
def checkUnit (u : UnitData) (fileRefs : Array ByteArray)
    (hasher : CA.SHA256.Hasher := CA.SHA256.pureHasher) : IO (Except String Checked) := do
  let mut base : RefTable := {}
  for j in [:u.refs.size] do
    match fileRefs[u.refs[j]!]? with
    | some id => base := base.insert (refPlaceholder j) id
    | none => return .error s!"reference {j}: file position {u.refs[j]!} out of range"
  let name : RRef → Name
    | .self => memberPlaceholder 0
    | .ref j => refPlaceholder j
    | .member i => memberPlaceholder i
    | .byName n => n
  let level (k : Nat) : Name := Name.mkSimple s!"u_{k}"
  let es := u.exprs name level (fun _ => .anonymous)
  let lps (n : Nat) : List Name := (List.range n).map level
  match u.form with
  | .statement =>
    let m := u.members[0]!
    let (s, unres) ← CA.RefHash.stmtIdOf (lps m.numLevels) es[m.type]! base hasher
    return .ok { form := .statement, key := s, ids := #[(s, s, s)], unresolved := unres }
  | form =>
    let thmValues := u.members.filterMap fun m => match m.fields with
      | .thm v _ => some v.isSome | _ => none
    let withProofs := thmValues.all id
    if !withProofs && thmValues.any id then
      return .error "theorems with and without values in one unit"
    let mut decls := #[]
    for i in [:u.members.size] do
      decls := decls.push (memberPlaceholder i,
        u.constantInfo es i name (lps u.members[i]!.numLevels))
    let (ids, _) ← CA.RefHash.computeIds decls base hasher withProofs
    if ids.size != u.members.size then return .error "member count changed"
    let unresolved := (ids.foldl (fun s d => d.unresolved.foldl (·.insert ·) s) ({} : NameSet)).toArray
      |>.filter (!isPlaceholder ·)
    let triples := ids.map fun d => (d.stmt, d.decl, d.ref)
    if form == .standalone then
      if ids[0]!.block.isSome then return .error "standalone unit forms a block"
      return .ok { form, key := ids[0]!.decl, ids := triples, unresolved }
    let some (b, _) := ids[0]!.block | return .error "block unit has no block id"
    for i in [:ids.size] do
      match ids[i]!.block with
      | some (b', k) =>
        if b' != b then return .error "members fall into different blocks"
        if k != i then return .error s!"member {i} is out of canonical order (should be {k})"
      | none => return .error s!"member {i} is not in the block"
    return .ok { form, key := b, ids := triples, unresolved }

/-! ## Encoding -/

private structure EncState where
  nodes : Array Node := #[]
  nodePos : Std.HashMap Node Nat := {}
  exprMemo : Std.HashMap ExprStructEq Nat := {}
  refs : Array ByteArray := #[]
  /-- One slot per distinct (id, name): two names sharing an id get two slots. -/
  refPos : Std.HashMap (ByteArray × Name) Nat := {}
  refName : Array Name := #[]
  /-- Name of a slot whose id an earlier slot already has (first name, this one). -/
  collisions : Array (Name × Name) := #[]
  /-- Binder name slots, one per distinct binder name. -/
  binderSlots : Array Name := #[]
  binderPos : Std.HashMap Name Nat := {}

private abbrev EncM := StateT EncState (Except String)

/-- How the encoder resolves a constant name. -/
private inductive Res where
  | id (bytes : ByteArray) | member (i : Nat) | byName

private def rrefOf (res : Name → Res) (n : Name) : EncM RRef := do
  match res n with
  | .member i => return .member i
  | .byName => return .byName n
  | .id bytes =>
    let s ← get
    match s.refPos.get? (bytes, n) with
    | some j => return .ref j
    | none =>
      let collisions := match s.refs.idxOf? bytes with
        | some j => s.collisions.push (s.refName[j]!, n)
        | none => s.collisions
      set { s with refs := s.refs.push bytes, refPos := s.refPos.insert (bytes, n) s.refs.size,
                   refName := s.refName.push n, collisions }
      return .ref s.refs.size

private def emit (e : Expr) (n : Node) : EncM Nat := do
  let s ← get
  match s.nodePos.get? n with
  | some i =>
    set { s with exprMemo := s.exprMemo.insert ⟨e⟩ i }
    return i
  | none =>
    let i := s.nodes.size
    set { s with nodes := s.nodes.push n, nodePos := s.nodePos.insert n i,
                 exprMemo := s.exprMemo.insert ⟨e⟩ i }
    return i

private def binderSlot (x : Name) : EncM Nat := do
  let s ← get
  match s.binderPos.get? x with
  | some k => return k
  | none =>
    set { s with binderSlots := s.binderSlots.push x, binderPos := s.binderPos.insert x s.binderSlots.size }
    return s.binderSlots.size

/-- Node index of a canonical expression. Children first (post-order,
    left to right); a node equal to an earlier one up to names is that
    node (`nodePos` is keyed by the node with names erased). -/
private partial def encExpr (res : Name → Res) (e : Expr) : EncM Nat := do
  if let some i := (← get).exprMemo.get? ⟨e⟩ then return i
  let lv (l : Level) : EncM PLevel := match PLevel.ofLevel l with
    | .ok p => pure p | .error err => throw err
  match e with
  | .mdata _ x => encExpr res x
  | .bvar i => emit e (.bvar i)
  | .sort l => emit e (.sort (← lv l))
  | .const c ls =>
    let r ← rrefOf res c
    emit e (.const r (← ls.mapM lv))
  | .app f a =>
    let fi ← encExpr res f
    let ai ← encExpr res a
    emit e (.app fi ai)
  | .lam x t b bi =>
    let k ← binderSlot x
    let ti ← encExpr res t
    let bi' ← encExpr res b
    emit e (.lam bi k ti bi')
  | .forallE x t b bi =>
    let k ← binderSlot x
    let ti ← encExpr res t
    let bi' ← encExpr res b
    emit e (.forallE bi k ti bi')
  | .letE x t v b nd =>
    let k ← binderSlot x
    let ti ← encExpr res t
    let vi ← encExpr res v
    let bi ← encExpr res b
    emit e (.letE k nd ti vi bi)
  | .lit (.natVal n) => emit e (.natLit n)
  | .lit (.strVal s) => emit e (.strLit s)
  | .proj S i s =>
    let r ← rrefOf res S
    let si ← encExpr res s
    emit e (.proj r i si)
  | .fvar _ | .mvar _ => throw "free or meta variable in a kernel declaration"

private def canon (ci : ConstantInfo) (e : Expr) : Expr :=
  CA.Canonical.canonicalizeL0Decl ci.levelParams e

/-- Encode one member's fields; `allRef` turns a name in `all` into a reference. -/
private def encMember (res : Name → Res) (allRef : Name → EncM RRef) (ci : ConstantInfo)
    (withProofs : Bool) : EncM Member := do
  let type ← encExpr res (canon ci ci.type)
  let refs (ns : List Name) : EncM (Array RRef) := ns.toArray.mapM allRef
  let fields ← match ci with
    | .axiomInfo v => pure (Fields.axiom v.isUnsafe)
    | .defnInfo v =>
      let x ← encExpr res (canon ci v.value)
      pure (.defn v.safety x (← refs v.all))
    | .thmInfo v =>
      let x ← if withProofs then some <$> encExpr res (canon ci v.value) else pure none
      pure (.thm x (← refs v.all))
    | .opaqueInfo v =>
      let x ← encExpr res (canon ci v.value)
      pure (.opaque v.isUnsafe x (← refs v.all))
    | .quotInfo v => pure (.quot v.kind)
    | .inductInfo v =>
      pure (.induct v.numParams v.numIndices v.numNested v.isRec v.isUnsafe v.isReflexive
        (← refs v.ctors) (← refs v.all))
    | .ctorInfo v =>
      pure (.ctor (← allRef v.induct) v.cidx v.numParams v.numFields v.isUnsafe)
    | .recInfo v =>
      let mut rules := #[]
      for r in v.rules do
        let c ← allRef r.ctor
        let rhs ← encExpr res (canon ci r.rhs)
        rules := rules.push (c, r.nfields, rhs)
      pure (.recursor v.numParams v.numIndices v.numMotives v.numMinors v.k v.isUnsafe
        rules (← refs v.all))
  return { numLevels := ci.levelParams.length, type, fields }

structure Encoded where
  form : Form
  key : ByteArray
  bytes : ByteArray
  data : UnitData
  /-- Ids per member, in member order (what `computeIds` returned). -/
  ids : Array DeclIds
  /-- One per member, in member order: `(name, decoration bytes)`. -/
  decorations : Array (Name × ByteArray)
  /-- Every member rebuilt from the unit and its decoration equals the
      input up to level normalisation and `mdata`. `false` means some
      name could not be told apart on a shared node (twins referenced
      together, or one subterm under two binder names). -/
  exact : Bool
  /-- Members that did not come back exactly. -/
  inexact : Array Name := #[]
  /-- Pairs of distinct names sharing one reference position (first name, other). -/
  collisions : Array (Name × Name) := #[]

/-- Structural equality that keeps constant names, and binder names when
    `binderNames`, but not universe parameter names, level syntax or
    `mdata`. -/
def sameExpr (lpsA lpsB : List Name) (a b : Expr) (binderNames := true) : Bool :=
  let a := CA.Canonical.canonicalizeL0Decl lpsA a
  let b := CA.Canonical.canonicalizeL0Decl lpsB b
  if binderNames then a.equal b else a == b

def sameConstant (a b : ConstantInfo) (binderNames := true) : Bool :=
  let e (x y : Expr) := sameExpr a.levelParams b.levelParams x y binderNames
  a.name == b.name && a.levelParams == b.levelParams && e a.type b.type &&
  match a, b with
  | .axiomInfo x, .axiomInfo y => x.isUnsafe == y.isUnsafe
  | .defnInfo x, .defnInfo y => e x.value y.value && x.safety == y.safety && x.all == y.all &&
      x.hints == y.hints
  | .thmInfo x, .thmInfo y => e x.value y.value && x.all == y.all
  | .opaqueInfo x, .opaqueInfo y => e x.value y.value && x.isUnsafe == y.isUnsafe && x.all == y.all
  | .quotInfo x, .quotInfo y => x.kind == y.kind
  | .inductInfo x, .inductInfo y => x.numParams == y.numParams && x.numIndices == y.numIndices &&
      x.all == y.all && x.ctors == y.ctors && x.numNested == y.numNested && x.isRec == y.isRec &&
      x.isUnsafe == y.isUnsafe && x.isReflexive == y.isReflexive
  | .ctorInfo x, .ctorInfo y => x.induct == y.induct && x.cidx == y.cidx &&
      x.numParams == y.numParams && x.numFields == y.numFields && x.isUnsafe == y.isUnsafe
  | .recInfo x, .recInfo y => x.all == y.all && x.numParams == y.numParams &&
      x.numIndices == y.numIndices && x.numMotives == y.numMotives &&
      x.numMinors == y.numMinors && x.k == y.k && x.isUnsafe == y.isUnsafe &&
      x.rules.length == y.rules.length &&
      (x.rules.zip y.rules).all fun (r, s) => r.ctor == s.ctor && r.nfields == s.nfields && e r.rhs s.rhs
  | _, _ => false

/-- Encode one strongly connected component: a standalone constant or a
    whole block, with every external reference in `table`. Members come
    out in canonical order (`spec.md` §9.4) with their ids; decorations
    cite `ft`, which is returned extended. -/
def encodeUnit (decls : Array (Name × ConstantInfo)) (table : RefTable) (ft : FileTable)
    (hasher : CA.SHA256.Hasher := CA.SHA256.pureHasher) (withProofs : Bool := true) :
    IO (Except String (Encoded × FileTable)) := do
  if decls.isEmpty then return .error "nothing to encode"
  let (ids, _) ← CA.RefHash.computeIds decls table hasher withProofs
  let byName : Std.HashMap Name ConstantInfo := decls.foldl (fun m (n, ci) => m.insert n ci) {}
  -- Canonical member order, and the form.
  let mut form0 := Form.standalone
  let mut members0 : Array DeclIds := #[]
  let mut key0 : ByteArray := .empty
  if ids.size == 1 && ids[0]!.block.isNone then
    members0 := #[ids[0]!]
    key0 := ids[0]!.decl
  else
    form0 := .block
    let mut placed : Array (Nat × DeclIds) := #[]
    for d in ids do
      match d.block with
      | some (b, i) =>
        if !key0.isEmpty && b != key0 then
          return .error "input is not one strongly connected component"
        key0 := b
        placed := placed.push (i, d)
      | none => return .error "input is not one strongly connected component"
    members0 := (placed.qsort (·.1 < ·.1)).map (·.2)
  let form := form0
  let members := members0
  let key := key0
  let posOf : Std.HashMap Name Nat := Id.run do
    let mut m := {}
    if form == .block then
      for i in [:members.size] do m := m.insert members[i]!.name i
    return m
  let res (n : Name) : Res :=
    match posOf.get? n with
    | some i => .member i
    | none => match table.get? n with
      | some r => .id r
      | none => .byName
  let enc : EncM (Array Member) := do
    let mut ms := #[]
    for d in members do
      let ci := byName.get! d.name
      let allRef (n : Name) : EncM RRef :=
        if form == .standalone && n == d.name then pure .self else rrefOf res n
      ms := ms.push (← encMember res allRef ci withProofs)
    return ms
  match enc.run {} with
  | .error e => return .error e
  | .ok (ms, st) =>
    let mut ft := ft
    let mut fileRefs := #[]
    for id in st.refs do
      let (ft', i) := ft.refIx id
      ft := ft'
      fileRefs := fileRefs.push i
    let data : UnitData := { form, refs := fileRefs, nodes := st.nodes, members := ms }
    let mut refNames := #[]
    for n in st.refName do
      let (ft', i) := ft.nameIx n
      ft := ft'
      refNames := refNames.push i
    let binders := st.binderSlots
    let mut decos : Array Decoration := #[]
    for i in [:members.size] do
      let ci := byName.get! members[i]!.name
      let hints := match ci with | .defnInfo v => some v.hints | _ => none
      let d : Decoration := ⟨ci.name, i, refNames, ci.levelParams.toArray, binders, hints⟩
      decos := decos.push d
    -- Self-check: rebuild and compare.
    let mut inexact := #[]
    match rebuild data ft decos with
    | .error e => return .error s!"rebuild failed: {e}"
    | .ok back =>
      for i in [:members.size] do
        let orig := byName.get! members[i]!.name
        let (_, ci) := back[i]!
        let orig := if withProofs then orig else match orig with
          | .thmInfo v => .thmInfo { v with value := .sort .zero }
          | c => c
        if !sameConstant orig ci then inexact := inexact.push orig.name
    let out : Encoded := ⟨form, key, data.toBytes, data, members,
      decos.map fun d => (d.own, d.toBytes), inexact.isEmpty, inexact, st.collisions⟩
    return .ok (out, ft)

/-- Encode a bare statement (the type of a theorem, with its universe
    binders) as a statement unit. Its key is the `stmt` any theorem of
    that type gets. -/
def encodeStatement (levelParams : List Name) (type : Expr) (table : RefTable) (ft : FileTable)
    (hasher : CA.SHA256.Hasher := CA.SHA256.pureHasher) :
    IO (Except String (Encoded × FileTable)) := do
  let (s, unres) ← CA.RefHash.stmtIdOf levelParams type table hasher
  let res (n : Name) : Res := match table.get? n with
    | some r => .id r
    | none => .byName
  let e := CA.Canonical.canonicalizeL0Decl levelParams type
  match (encExpr res e).run {} with
  | .error err => return .error err
  | .ok (ty, st) =>
    let mut ft := ft
    let mut fileRefs := #[]
    for id in st.refs do
      let (ft', i) := ft.refIx id
      ft := ft'
      fileRefs := fileRefs.push i
    let m : Member := ⟨levelParams.length, ty, .thm none #[]⟩
    let data : UnitData := ⟨.statement, fileRefs, st.nodes, #[m]⟩
    let ids : DeclIds := { name := .anonymous, stmt := s, decl := s, ref := s, unresolved := unres }
    let out : Encoded := ⟨.statement, s, data.toBytes, data, #[ids], #[], true, #[], st.collisions⟩
    return .ok (out, ft)

end CA.Payload

import Lean
import CA.Canonical
import CA.RefHash
import CA.SHA256
import CA.Util

open Lean Meta
open CA.Canonical
open CA.SHA256
open CA.Util

namespace CA.ExprHash

/-! ## ByteArray Serialization Helpers -/

private def pushTag (buf : ByteArray) (tag : UInt8) : ByteArray :=
  buf.push tag

private def pushUInt64 (buf : ByteArray) (n : UInt64) : ByteArray := Id.run do
  let mut b := buf
  let mut v := n
  for _ in List.range 8 do
    b := b.push (v &&& 0xFF).toUInt8
    v := v >>> 8
  return b

private def pushNat (buf : ByteArray) (n : Nat) : ByteArray :=
  pushUInt64 buf n.toUInt64

private def pushString (buf : ByteArray) (s : String) : ByteArray :=
  let bytes := s.toUTF8
  let buf := pushNat buf bytes.size
  buf ++ bytes

/-- Arbitrary-precision `Nat` (for literals): length-prefixed minimal
    big-endian bytes. `pushNat` truncates to 64 bits, which made every
    literal `≥ 2^64` collide with its residue (scheme 0). -/
private def pushNatBig (buf : ByteArray) (n : Nat) : ByteArray :=
  let bytes := natToBytesBE n
  (pushNat buf bytes.size) ++ bytes

private def pushName (buf : ByteArray) (n : Name) : ByteArray :=
  pushString buf n.toString

private def pushBinderInfo (buf : ByteArray) : BinderInfo → ByteArray
  | .default => buf.push 0
  | .implicit => buf.push 1
  | .strictImplicit => buf.push 2
  | .instImplicit => buf.push 3

private partial def pushLevel (buf : ByteArray) (l : Level) : ByteArray :=
  match l with
  | .zero => pushTag buf 0x10
  | .succ l => pushLevel (pushTag buf 0x11) l
  | .max l1 l2 => pushLevel (pushLevel (pushTag buf 0x12) l1) l2
  | .imax l1 l2 => pushLevel (pushLevel (pushTag buf 0x13) l1) l2
  | .param name => pushName (pushTag buf 0x14) name
  | .mvar id => pushName (pushTag buf 0x15) id.name

/-! ## Structural Serialization (`type_hash` scheme 1, retired)

Serialize an Expr into a ByteArray with tag bytes for each constructor,
`.const` nodes carrying the constant's *name*. SHA-256 of this was the
name-based `type_hash` up to CA v0.3.1 (scheme 1). It walks the **tree**,
so its cost is the tree's size, unbounded in the DAG's: CA no longer
hashes with it. The name-based hashes are now `CA.RefHash.typeHashOf`
and `valueHashOf` (scheme 2, Merkle, memoised: the DAG's cost), which
`computeNameBasedHashes` below uses. The serialisation itself remains, as
a payload format (canode stores small types with it, behind a node
cap), not as an id. -/

/-- Serialize an Expr into a ByteArray. Each constructor gets a unique tag byte
    followed by its serialized children. A tree walk: never call it on a
    term whose tree may be large. -/
partial def serializeExpr (e : Expr) (buf : ByteArray := .empty) : ByteArray :=
  match e with
  | .bvar n => pushNat (pushTag buf 0x01) n
  | .fvar id => pushName (pushTag buf 0x02) id.name
  | .mvar id => pushName (pushTag buf 0x03) id.name
  | .sort l => pushLevel (pushTag buf 0x04) l
  | .const name levels =>
    let buf := pushName (pushTag buf 0x05) name
    levels.foldl (fun b l => pushLevel b l) buf
  | .app f a =>
    let buf := serializeExpr f (pushTag buf 0x06)
    serializeExpr a buf
  | .lam _ t b bi =>
    let buf := pushBinderInfo (pushTag buf 0x07) bi
    let buf := serializeExpr t buf
    serializeExpr b buf
  | .forallE _ t b bi =>
    let buf := pushBinderInfo (pushTag buf 0x08) bi
    let buf := serializeExpr t buf
    serializeExpr b buf
  | .letE _ t v b _ =>
    let buf := serializeExpr t (pushTag buf 0x09)
    let buf := serializeExpr v buf
    serializeExpr b buf
  | .lit (.natVal n) => pushNatBig (pushTag buf 0x0A) n
  | .lit (.strVal s) => pushString (pushTag buf 0x0B) s
  | .mdata _ e => serializeExpr e buf
  | .proj t i e =>
    let buf := pushName (pushTag buf 0x0C) t
    let buf := pushNat buf i
    serializeExpr e buf

/-! ## Hex Formatting -/

/-- Format a ByteArray hash as a hex string. -/
def toHex := toHex256

/-! ## Declaration Hash Structure -/

/-- Sentinel value hash for theorems (proof irrelevance). -/
def proofIrrelevantHash : String := "PROOF_IRRELEVANT"

/-- Content-addressed hash data for a single declaration. -/
structure DeclHash where
  name       : Name
  module     : Name            -- source module
  kind       : String
  typeHash   : String          -- hex `type_hash` (scheme 2, `RefHash.typeHashOf`)
  valueHash  : Option String   -- hex value hash (`RefHash.valueHashOf`), or sentinel
  ppType     : String          -- pretty-printed type
  typeDeps   : Array Name      -- constants referenced in the type
  valueDeps  : Array Name      -- constants referenced in the value
  deriving Inhabited

/-- Resolve the module that owns a declaration. Declarations with no
    module index belong to the module currently being elaborated, so the
    fallback is `env.mainModule` (`.anonymous` only when that is unset). -/
def getModuleName (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx =>
    let mods := env.allImportedModuleNames
    if h : idx.toNat < mods.size then mods[idx.toNat] else env.mainModule
  | none => env.mainModule

/-! ## Batch Hash Computation

For L1, types are normalized with native `whnf` via micro-batches (fresh MetaM
per batch of ≤10 declarations) to prevent state accumulation → SIGSEGV.
Values always use L0 (pure) canonicalization — whnf on definition values causes
cumulative process-level memory growth that crashes after ~30k declarations
regardless of batch size. L0 uses a single session.

See `docs/l1-normalization.md` for the full crash analysis. -/

/-- Default micro-batch size for L1 whnf processing. Each batch gets a fresh
    MetaM session to prevent native whnf state accumulation crashes.
    Empirically: batch 10 works, batch 20 crashes. -/
private def defaultL1BatchSize : Nat := 10

/-- Intermediate hash data before pretty-printing (avoids ppExpr in whnf batch). -/
private structure PreDeclHash where
  name       : Name
  module     : Name
  kind       : String
  typeHash   : String
  valueHash  : Option String
  canonType  : Expr           -- for ppExpr in a separate pass
  typeDeps   : Array Name
  valueDeps  : Array Name
  deriving Inhabited

/-- The type to hash at a given level, before universe renaming (the
    hash renames positionally from the declaration's `levelParams`): the
    type itself for L0, its reducible normal form for L1. -/
private def mkNormFn (level : CanonLevel) : Expr → MetaM Expr := fun e =>
  match level with
  | .l0 => pure e
  | .l1 => deepNormalize e

/-- Hash the value of a declaration at L0 (`RefHash.valueHashOf`).
    Values always use L0 — whnf on definition values causes cumulative
    memory growth → SIGSEGV after ~30k declarations. -/
private def hashValue (ci : ConstantInfo) (hasher : Hasher) (shared : CA.RefHash.SharedMemo) :
    IO (Option String × Array Name) := do
  match ci with
  | .thmInfo ti =>
    let vdeps := (collectConstants ti.value).toList.toArray
    pure (some proofIrrelevantHash, vdeps)
  | .defnInfo di =>
    let vh ← CA.RefHash.valueHashOf ci.levelParams di.value hasher shared
    pure (some (toHex vh), (collectConstants di.value).toList.toArray)
  | .opaqueInfo oi =>
    let vh ← CA.RefHash.valueHashOf ci.levelParams oi.value hasher shared
    pure (some (toHex vh), (collectConstants oi.value).toList.toArray)
  | _ => pure (none, #[])

/-- Phase 1: Canonicalize + hash a batch in a single MetaM session (no ppExpr).
    Returns pre-hashes and the number of declarations that fell back to L0. -/
private def hashBatchPhase1 (env : Environment) (batch : Array (Name × ConstantInfo))
    (normFn : Expr → MetaM Expr) (hasher : Hasher) (shared : CA.RefHash.SharedMemo) :
    IO (Array PreDeclHash × Nat) := do
  runMetaM env do
    let mut results : Array PreDeclHash := #[]
    let mut fallbacks : Nat := 0
    for (name, ci) in batch do
      let normType ← try
        normFn ci.type
      catch e =>
        fallbacks := fallbacks + 1
        IO.eprintln s!"  Warning: L1 failed on {name}: {← e.toMessageData.toString}"
        pure ci.type
      let typeH := toHex (← CA.RefHash.typeHashOf ci.levelParams normType hasher shared)
      let typeDeps := (collectConstants ci.type).toList.toArray
      let mod := getModuleName env name

      let (valueH, valueDeps) ← hashValue ci hasher shared

      results := results.push {
        name, module := mod, kind := constantKind ci, typeHash := typeH,
        valueHash := valueH, canonType := canonicalizeL0 normType,
        typeDeps, valueDeps
      }
    return (results, fallbacks)

/-- Phase 2: Pretty-print canonical types in a fresh MetaM session (no whnf pressure). -/
private def hashBatchPhase2 (env : Environment)
    (preHashes : Array PreDeclHash) : IO (Array DeclHash) := do
  runMetaM env do
    let mut results : Array DeclHash := #[]
    for ph in preHashes do
      let fmt ← ppExpr ph.canonType
      let ppT := fmt.pretty
      results := results.push {
        name := ph.name, module := ph.module, kind := ph.kind,
        typeHash := ph.typeHash, valueHash := ph.valueHash,
        ppType := ppT,
        typeDeps := ph.typeDeps, valueDeps := ph.valueDeps
      }
    return results

/-- Number of declarations to accumulate before flushing PreDeclHash → DeclHash.
    Bounds the number of live canonical Expr objects in memory to prevent
    process-level memory growth that causes SIGSEGV in whnf. -/
private def flushInterval : Nat := 5000

/-- Compute name-based hashes for all declarations.
    For L0: single MetaM session (pure, no crash risk).
    For L1: micro-batches with fresh MetaM per batch (default 10).
    Every `flushInterval` declarations, ppExpr is run and Expr objects are
    released to prevent process memory growth.
    Pass `batchSize` to override (0 = use defaults); `hasher` selects the
    SHA-256 implementation (default pure Lean; same digests either way). -/
def computeNameBasedHashes (env : Environment) (decls : Array (Name × ConstantInfo))
    (level : CanonLevel) (batchSize : Nat := 0) (hasher : Hasher := pureHasher)
    : IO (Array DeclHash) := do
  let normFn := mkNormFn level
  -- One memo for the whole run: subterm ids do not depend on the root
  -- tag, so types and values share it (`RefHash.valueHashOf`).
  let shared : CA.RefHash.SharedMemo ← IO.mkRef {}
  let bs := if batchSize > 0 then batchSize
            else if level == .l1 then defaultL1BatchSize else decls.size
  let mut allResults : Array DeclHash := #[]
  let mut pendingPre : Array PreDeclHash := #[]
  let mut totalFallbacks : Nat := 0
  let mut batchStart : Nat := 0
  while batchStart < decls.size do
    let batchEnd := min (batchStart + bs) decls.size
    if batchStart % 1000 == 0 then
      IO.eprintln s!"  Normalizing: {batchStart}/{decls.size}"
    let batch := decls[batchStart:batchEnd]
    let (batchResults, fallbacks) ← hashBatchPhase1 env batch normFn hasher shared
    pendingPre := pendingPre ++ batchResults
    totalFallbacks := totalFallbacks + fallbacks
    batchStart := batchEnd
    -- Flush: ppExpr pending PreDeclHashes and release canonical Expr objects
    if pendingPre.size ≥ flushInterval || batchStart ≥ decls.size then
      if level == .l1 then
        IO.eprintln s!"  Pretty-printing: {pendingPre.size} (total so far: {allResults.size + pendingPre.size})"
      let flushed ← hashBatchPhase2 env pendingPre
      allResults := allResults ++ flushed
      pendingPre := #[]
  if totalFallbacks > 0 then
    IO.eprintln s!"  Warning: {totalFallbacks} declarations fell back to L0 normalization"
  return allResults

end CA.ExprHash

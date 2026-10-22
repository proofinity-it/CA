import Lean

open Lean Meta

namespace CA.Canonical

/-! ## Level 0 Canonicalization (Pure)

Level 0 ensures α-equivalence:
- Renames universe parameters to positional indices (`u_0`, `u_1`, ...)
- Normalises universe levels (`Level.normalize`, after renaming)
- Strips `.mdata` annotations (irrelevant to mathematical content)
- Binder names are never serialised by the hashing modules (bound variables
  are de Bruijn indices), so nothing needs stripping for them.
-/

/-- Collect all `Level.param` names from a `Level`, preserving first-occurrence order. -/
partial def collectLevelParams (l : Level)
    (seen : Std.HashSet Name) (order : Array Name) : Std.HashSet Name × Array Name :=
  match l with
  | .param name =>
    if seen.contains name then (seen, order)
    else (seen.insert name, order.push name)
  | .succ l => collectLevelParams l seen order
  | .max l1 l2 =>
    let (seen, order) := collectLevelParams l1 seen order
    collectLevelParams l2 seen order
  | .imax l1 l2 =>
    let (seen, order) := collectLevelParams l1 seen order
    collectLevelParams l2 seen order
  | .zero => (seen, order)
  | .mvar _ => (seen, order)

/-- Walk an `Expr` to collect all universe parameter names in
    first-occurrence order.

    Sharing-aware: a subterm that has already been visited (structurally
    equal, `ExprStructEq`) contributes nothing new, so it is skipped, and a subterm without
    level parameters (`Expr.hasLevelParam`) is not entered at all. The
    order of first occurrences is exactly the plain DFS order — the
    result is identical to a naive walk, but the cost is the size of the
    DAG rather than of the unfolded tree (the naive walk was exponential
    on `omega`/`decide` proof terms). -/
partial def collectExprUnivParams (e : Expr)
    (seen : Std.HashSet Name) (order : Array Name) : Std.HashSet Name × Array Name :=
  let (_, seen, order) := go e {} seen order
  (seen, order)
where
  go (e : Expr) (visited : Std.HashSet ExprStructEq) (seen : Std.HashSet Name) (order : Array Name)
      : Std.HashSet ExprStructEq × Std.HashSet Name × Array Name :=
    if !e.hasLevelParam then (visited, seen, order)
    else if visited.contains ⟨e⟩ then (visited, seen, order)
    else
      let visited := visited.insert ⟨e⟩
      match e with
      | .const _ levels =>
        let (seen, order) := levels.foldl (fun (seen, order) l => collectLevelParams l seen order) (seen, order)
        (visited, seen, order)
      | .sort level =>
        let (seen, order) := collectLevelParams level seen order
        (visited, seen, order)
      | .app f a =>
        let (visited, seen, order) := go f visited seen order
        go a visited seen order
      | .lam _ ty body _ =>
        let (visited, seen, order) := go ty visited seen order
        go body visited seen order
      | .forallE _ ty body _ =>
        let (visited, seen, order) := go ty visited seen order
        go body visited seen order
      | .letE _ ty value body _ =>
        let (visited, seen, order) := go ty visited seen order
        let (visited, seen, order) := go value visited seen order
        go body visited seen order
      | .mdata _ e => go e visited seen order
      | .proj _ _ e => go e visited seen order
      | _ => (visited, seen, order)

/-- Build canonical mapping: first occurrence → `u_0`, `u_1`, ... -/
def buildCanonicalUnivMapping (params : Array Name) : Std.HashMap Name Name := Id.run do
  let mut mapping : Std.HashMap Name Name := {}
  for i in [:params.size] do
    mapping := mapping.insert params[i]! (Name.mkSimple s!"u_{i}")
  return mapping

/-- Apply canonical mapping to a `Level`, then normalise it
    (`Level.normalize`): `max u v` / `max v u`, `max u u` / `u`,
    `imax u (v+1)` / `max u (v+1)` are definitionally equal levels and must
    hash alike. Normalisation runs *after* renaming because
    `Level.normalize` orders parameters by `Name.lt`, so the normal form
    would otherwise depend on the original parameter names. -/
partial def canonicalizeLevel (l : Level) (mapping : Std.HashMap Name Name) : Level :=
  (go l).normalize
where
  go : Level → Level
    | .param name => .param (mapping.getD name name)
    | .succ l => .succ (go l)
    | .max l1 l2 => .max (go l1) (go l2)
    | .imax l1 l2 => .imax (go l1) (go l2)
    | l => l

/-- Apply canonical universe mapping (and level normalisation) throughout
    an `Expr`. Also strips `.mdata`. Implemented with `Expr.replace` (the
    runtime's cached, sharing-preserving traversal): unchanged subterms —
    including `.const`/`.sort` nodes whose levels are already canonical —
    are the same objects as in the input, so a DAG-shaped proof term
    stays a DAG. -/
partial def canonicalizeExprUnivs (e : Expr) (mapping : Std.HashMap Name Name) : Expr :=
  e.replace fun s => match s with
    | .const name levels =>
      let levels' := levels.map fun l => canonicalizeLevel l mapping
      if levels' == levels then none else some (.const name levels')
    | .sort level =>
      let level' := canonicalizeLevel level mapping
      if level' == level then none else some (.sort level')
    | .mdata _ inner => some (canonicalizeExprUnivs inner mapping)
    | _ => none

/-- Strip `.mdata` recursively without changing anything else
    (sharing-preserving, via `Expr.replace`). -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun s => match s with
    | .mdata _ inner => some (stripMData inner)
    | _ => none

/-- Level 0 canonicalization (pure):
    1. Collect universe params in first-occurrence order
    2. Rename to positional names (u_0, u_1, ...)
    3. Normalise every universe level (`Level.normalize`)
    4. Strip `.mdata` annotations

    Step 3 runs even when the expression has no level parameters: closed
    levels such as `max 1 1` arise from instantiation and must agree with
    their normal form.

    Every step preserves sharing (see the helpers above); the previous
    implementation rebuilt the whole unfolded tree, which for a
    DAG-shaped proof term of a few million shared nodes meant tens of
    gigabytes of fresh `Expr` nodes — the memory blow-up that killed the
    first schema-v3 store rebuild (2026-08-18). -/
def canonicalizeL0 (e : Expr) : Expr :=
  let mapping : Std.HashMap Name Name :=
    if !e.hasLevelParam then {}
    else
      let (_, params) := collectExprUnivParams e {} #[]
      buildCanonicalUnivMapping params
  canonicalizeExprUnivs e mapping

/-- L0 canonicalization for the expressions of a *declaration* whose
    universe binder list is `levelParams`: parameters are renamed
    positionally (`levelParams[i] ↦ u_i`) and `.mdata` is stripped.

    First-occurrence renaming (`canonicalizeL0`) is the right notion for a
    free-standing expression, but for a declaration it forgets which binder
    position each parameter occupies — and use sites instantiate levels
    positionally. Independent first-occurrence renaming made
    `def q1.{u,v} : F u v` and `def q2.{u,v} : F v u` collide even though
    `q1.{a,b}` and `q2.{a,b}` have different types (and it lost the
    type↔value parameter correlation, since the two were renamed
    independently). Positional renaming keeps identity invariant under
    renaming the binders while staying sensitive to their order — exactly
    the α-equivalence of universe-polymorphic declarations.

    Parameters occurring in `e` but missing from `levelParams` (ill-formed
    input; the kernel would reject it) are appended in first-occurrence
    order, so the function is total and deterministic. Levels are
    normalised after renaming (see `canonicalizeLevel`). -/
def canonicalizeL0Decl (levelParams : List Name) (e : Expr) : Expr :=
  let mapping : Std.HashMap Name Name :=
    if !e.hasLevelParam then {}
    else
      let declared := levelParams.toArray
      let (_, occurring) := collectExprUnivParams e {} #[]
      let declaredSet : Std.HashSet Name := declared.foldl (·.insert ·) {}
      let extra := occurring.filter (!declaredSet.contains ·)
      buildCanonicalUnivMapping (declared ++ extra)
  canonicalizeExprUnivs e mapping

/-! ## Level 1 Canonicalization (MetaM)

Level 1 extends Level 0 with reducible-transparency normalization via
`deepNormalize`, which recursively applies `whnf` at every subexpression
under `withTransparency .reducible`. Properly opens binders with
`withLocalDecl` to avoid loose-bvar panics. Handles δ/β/ι/ζ/projection
reduction.

**Caveat:** Native `whnf` causes SIGSEGV after ~15-25k declarations in a
single MetaM session due to state accumulation (see `docs/l1-normalization.md`).
Callers must use micro-batching (fresh `runMetaM` per batch of ≤10 declarations).
`ExprHash.computeNameBasedHashes` handles this automatically.
-/

/-- Maximum recursion depth for `deepNormalize`. -/
def maxNormDepth : Nat := 256

/-- Deep normalization: recursively apply native `whnf` at every subexpression
    under reducible transparency. Properly opens binders with `withLocalDecl`
    to avoid "loose bvar" panics. Requires micro-batching to avoid SIGSEGV
    from MetaM state accumulation (see `docs/l1-normalization.md`). -/
partial def deepNormalize (e : Expr) (depth : Nat := 0) : MetaM Expr := do
  if depth ≥ maxNormDepth then return e
  withTransparency .reducible do
    let e ← whnf e
    match e with
    | .app f a =>
      return .app (← deepNormalize f (depth + 1)) (← deepNormalize a (depth + 1))
    | .lam n t b bi =>
      let t' ← deepNormalize t (depth + 1)
      withLocalDecl n bi t' fun x => do
        let b' ← deepNormalize (b.instantiate1 x) (depth + 1)
        mkLambdaFVars #[x] b'
    | .forallE n t b bi =>
      let t' ← deepNormalize t (depth + 1)
      withLocalDecl n bi t' fun x => do
        let b' ← deepNormalize (b.instantiate1 x) (depth + 1)
        mkForallFVars #[x] b'
    | .letE _ _ v b _ =>
      let v' ← deepNormalize v (depth + 1)
      deepNormalize (b.instantiate1 v') (depth + 1)
    | .mdata _ e => deepNormalize e depth
    | .proj t i e =>
      let e' ← deepNormalize e (depth + 1)
      whnf (.proj t i e')
    | e => return e

/-- Level 1 normalization: native whnf deep normalization + Level 0. -/
def canonicalizeL1 (e : Expr) : MetaM Expr := do
  let normalized ← deepNormalize e
  return canonicalizeL0 normalized

/-- Canonicalization level selector. -/
inductive CanonLevel where
  | l0  -- Pure: universe renaming + mdata stripping
  | l1  -- MetaM: reducible normalization + L0
  deriving Repr, BEq

/-- Run a MetaM computation in IO with a given environment. -/
def runMetaM (env : Environment) (action : MetaM α) : IO α := do
  let ctx : Core.Context := { fileName := "", fileMap := .ofString "" }
  let st : Core.State := { env }
  let (result, _) ← (MetaM.run' action).toIO ctx st
  return result

end CA.Canonical

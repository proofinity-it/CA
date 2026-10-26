# L1 normalisation: reducible `whnf`, and why it is micro-batched

L1 is the optional second canonicalisation level of the **CLI**
(`ca address --level 1`, `ca fetch --level 1`). The registry
(`#ca_registry`) and `CA.RefHash` use L0 only. This note records what L1
does, the native-`whnf` crash that shaped its implementation, and the
batching design that avoids it.

## What L1 does

L0 canonicalisation is pure: rename universe parameters to positional
indices, normalise universe levels, strip `.mdata`. It makes
`theorem foo.{u, v}` and `theorem bar.{α, β}` hash equally when their
bodies are identical, but it cannot see through `@[reducible]` aliases.

L1 adds reducible-transparency normalisation via Lean's native `whnf`, so
that type-level abbreviations collapse — `a + b` (that is,
`@HAdd.hAdd Nat Nat Nat instHAddNat a b`) and a direct `@Nat.add a b`
reach the same canonical form. Equivalence classes are strictly larger
than L0's. Instance arguments are *not* unfolded at reducible
transparency, which is the intended behaviour: `Add Nat` stays `Add Nat`.

`deepNormalize` (`CA.Canonical`) applies `whnf` at every subexpression
under `withTransparency .reducible`:

```
deepNormalize(e, depth):
  if depth ≥ 256: return e
  e ← whnf e              -- native, under reducible transparency
  match e:
    .app f a       → .app (deepNormalize f) (deepNormalize a)
    .lam n t b bi  → normalise t; open the binder with withLocalDecl;
                     normalise the body; re-abstract with mkLambdaFVars
    .forallE ...   → same, re-abstract with mkForallFVars
    .letE _ _ v b  → normalise v; substitute into b; normalise b
    .mdata _ e     → deepNormalize e  (strip)
    .proj t i e    → normalise e; whnf the projection again
    _              → return e
```

Binders are opened with `withLocalDecl` and closed with `mkLambdaFVars` /
`mkForallFVars`, which avoids loose-bvar panics. `canonicalizeL1` runs
`deepNormalize` and then `canonicalizeL0`.

## The crash

Native `whnf` (`@[extern "lean_whnf"]`) has no heartbeat checks. When it
overruns a resource limit the result is an uncatchable SIGSEGV, not a
Lean exception; `try/catch` and `ulimit -s unlimited` do not help.

Running the normaliser over `Mathlib.Algebra.Group.Basic` (~58k
declarations) exposed two failure modes.

**Mode 1: MetaM state accumulation, on types.** One `MetaM` session over
all declaration types crashes after ~25k of them. A reproducer with four
modes isolated the cause:

| Experiment | Result | Conclusion |
|---|---|---|
| forward order, one `MetaM` | SIGSEGV at ~25k | baseline |
| the "crashing" declaration alone, fresh `MetaM` | no crash | not a bad declaration |
| every declaration in its own `MetaM` | all fine | not inherent to any expression |
| reverse order, one `MetaM` | SIGSEGV at ~20–25k, different declarations | the threshold is a *count* |

No declaration crashes `whnf` in isolation; the crash follows the number
of reductions performed in one session. The likely cause is growth of
`MetaM` internal state — the `whnf` cache, discrimination trees, instance
tables — until the native code exceeds a stack or memory limit. A
blocklist of "bad" declarations was tried and could not converge, which
is what one expects when the cause is cumulative.

**Mode 2: process-level memory growth, on values.** Normalising
definition *values* makes the process RSS grow monotonically and crash
after ~30k declarations regardless of batch size, even with a fresh
`MetaM` per declaration — normalised bodies survive as live `Expr`s in
the accumulated results.

Why every reduction path is exposed: `whnfCore` (Lean code) calls
`reduceMatcher?` → `whnfMatcher` → native `whnf`, and `unfoldDefinition?`
reaches the same place through smart unfolding and
`unfoldProjInstWhenInstances?`. Only the plain delta/beta functions
(`Environment.find?`, `ConstantInfo.value?`, `instantiateLevelParams`,
`betaRev`, `headBeta`) stay in pure Lean.

## The design that avoids it

**Micro-batching (mode 1).** Declarations are processed in batches of
≤ 10, each in a fresh `runMetaM` session, which discards the previous
session's caches. Empirically batch 10 works and batch 20 crashes. L0
needs no batching (one session, no `whnf`). If L1 throws on a
declaration, that declaration falls back to L0 and processing continues.

**L0-only values (mode 2).** `hashValue` canonicalises values with L0 at
every level: theorems get the `PROOF_IRRELEVANT` sentinel, definitions
and opaques get `canonicalizeL0` of the body. Types get L1, values get
L0.

**Two phases, flushed.** `hashBatchPhase1` canonicalises and hashes a
batch and keeps the canonical `Expr` in a `PreDeclHash`; `ppExpr` is
deliberately kept out of that session. Every 5000 declarations (and at
the end) `hashBatchPhase2` pretty-prints the pending batch in a separate
fresh session and the canonical `Expr`s are released, bounding live
objects.

```
while batchStart < decls.size:
    batch := decls[batchStart .. batchStart + 10]
    pendingPre += hashBatchPhase1 env batch          -- fresh MetaM
    batchStart += 10
    if pendingPre.size ≥ 5000 or done:
        allResults += hashBatchPhase2 env pendingPre  -- fresh MetaM
        pendingPre := []
```

| Parameter | Value | Why |
|---|---|---|
| L1 micro-batch size | 10 | largest batch that does not crash |
| L0 batch size | all | pure, no `whnf` |
| flush interval | 5000 | bounds live canonical `Expr`s |
| `deepNormalize` depth limit | 256 | guards against runaway recursion |
| value canonicalisation | always L0 | `whnf` on values crashes regardless of batching |

Measured on `Mathlib.Algebra.Group.Basic`, theorems only (57,613): L0
about 5 minutes; L1 with native `whnf` and no batching crashed after
~10k; L1 with the pure fallback below about 4.5 minutes.

## Fallback: a pure-Lean reducer

If a future toolchain changes `whnf` behaviour, a reducer that never
enters native code is available as a design:

```lean
private def tryUnfoldHead (e : Expr) : MetaM (Option Expr) := do
  let .const name lvls := e.getAppFn | return none
  unless (← isReducible name) do return none
  let some body := (← getEnv).find? name >>= (·.value?) | return none
  return some ((body.instantiateLevelParams (← getConstInfo name).levelParams lvls).betaRev e.getAppRevArgs)

private partial def safeDeltaBeta (e : Expr) (fuel : Nat := 64) : MetaM Expr := do
  if fuel == 0 then return e
  match ← tryUnfoldHead e with
  | some e' => safeDeltaBeta e' (fuel - 1)
  | none => return e
```

applied at every subexpression with the same depth limit. It does delta
and beta only — no iota, zeta, projection reduction or instance
synthesis — which is enough to collapse `@[reducible]` aliases, and it
cannot crash. It is not in the code today; micro-batched native `whnf`
is, because it reduces more.

## Open questions

- The SIGSEGV is arguably a Lean bug: a heartbeat check or stack guard in
  native `whnf` would turn it into a catchable exception. Worth reporting
  upstream with the count-based reproducer.
- `Lean.Meta.reduce` (with options such as `explicitOnly`) was not
  evaluated as a middle ground.
- L1 is unstable across Mathlib refactors by construction (what is
  reducible changes), which is one reason the registry key is L0.

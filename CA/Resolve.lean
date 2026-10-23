import Lean
import CA.Sources
import CA.Registry.Generate

/-!
# `#ca_lookup` and `resolve%`: a registry answered from inside Lean

Both read the project's `sources.json` (`CA.Sources`) and its folder
sources; node sources need the `ca` CLI.

* `#ca_lookup "<stmt | type_hash | name>"` prints every entry the folder
  sources hold for the query: status, who proved it, under which open
  points, the statement.

* `resolve% "<stmt>"` is a term: the constant that a source binds to that
  statement, **provided the constant is in the current environment and
  has that `stmt` here too** (its id is recomputed, so a source cannot
  bind an address to a declaration that means something else). When the
  constant is not in the environment, the error names the project and
  module to add. Bringing a declaration that is not in the environment
  into scope from a node file is `ca verify`'s machinery turned around
  (`docs/plan.md` item 2) and is not done here.
-/

open Lean Elab Command Term Meta

namespace CA.Resolve

/-- Sources of the current project, or an explanation why there are none. -/
def readSources : IO (Except String CA.Sources.SourcesFile) := do
  match ← CA.Sources.read with
  | none => return .error s!"no {CA.Sources.defaultPath} in the project root"
  | some r => return r

def lookup (q : CA.Sources.Query) : IO (Except String (Array CA.Sources.Hit × Array String)) := do
  match ← readSources with
  | .error e => return .error e
  | .ok sf => return .ok (← CA.Sources.lookupFolders sf q)

/-- `#ca_lookup "<query>"`: what the folder sources say about a statement
    id, a coarse hash or a name. -/
elab "#ca_lookup " q:str : command => do
  let query := CA.Sources.Query.parse q.getString
  match ← lookup query with
  | .error e => throwError "#ca_lookup: {e}"
  | .ok (hits, notes) =>
    let mut msg := m!"{query}: {hits.size} {if hits.size == 1 then "entry" else "entries"}"
    for h in hits do msg := msg ++ m!"\n  {h.describe}"
    for n in notes do msg := msg ++ m!"\n  note: {n}"
    logInfo msg

/-- The `stmt` of `n` in the current environment, base58, recomputed. -/
def stmtOf (env : Environment) (n : Name) : IO (Option String) := do
  let ids ← CA.Registry.computeEntryIds env #[n]
  return (ids.get? n).map fun i => CA.RefHash.toB58 i.stmt

/-- `resolve% "<stmt>"`: the constant a source binds to the statement, if it
    is in scope and has that statement here. -/
elab "resolve% " s:str : term => do
  let q := CA.Sources.Query.parse s.getString
  let want ← match q with
    | .stmt b => pure b
    | _ => throwError "resolve%: expected a statement id (base58, 32 bytes), got {q}"
  let (hits, notes) ← match ← lookup q with
    | .error e => throwError "resolve%: {e}"
    | .ok r => pure r
  if hits.isEmpty then
    let mut msg := m!"resolve%: no source binds statement {want}"
    for n in notes do msg := msg ++ m!"\n  note: {n}"
    throwError msg
  -- A proof of the statement is what a term position wants: theorems (and
  -- axioms) before the `def _ : Prop` that states it (an open point).
  let isProof (h : CA.Sources.Hit) := h.entry.kind == "theorem" || h.entry.kind == "axiom"
  let hits := hits.filter isProof ++ hits.filter (!isProof ·)
  let env ← getEnv
  let mut absent : Array CA.Sources.Hit := #[]
  let mut wrong : Array (CA.Sources.Hit × String) := #[]
  for h in hits do
    let n := h.entry.name
    if env.contains n then
      match ← stmtOf env n with
      | some s =>
        if s == want then
          return ← mkConstWithFreshMVarLevels n
        else wrong := wrong.push (h, s)
      | none => wrong := wrong.push (h, "(no id)")
    else absent := absent.push h
  let mut msg := m!"resolve%: statement {want} is bound by {hits.size} source {if hits.size == 1 then "entry" else "entries"}, none usable here:"
  for h in absent do
    msg := msg ++ m!"\n  {h.entry.name} ({h.source}, project {h.project}): not in this environment; add the project as a dependency and import {h.entry.module}"
  for (h, s) in wrong do
    msg := msg ++ m!"\n  {h.entry.name} ({h.source}): in this environment its statement is {s}, not {want}; the source and this build disagree (toolchain {h.toolchain} there)"
  throwError msg

end CA.Resolve

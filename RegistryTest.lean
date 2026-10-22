import Lean
import Lean.Elab.Frontend
import CA

/-!
Test executable for `CA.Registry` classification. Elaborates a small
source (which imports `CA`, so the attributes and `#ca_registry` are
available) and checks every status the generator can assign:

* a theorem whose type is an open point's constant, or whose address
  equals the open point's statement address, *proves* it: both are
  `proved`, the open point becomes `proved` with `proved_by`;
* a hypothesis that is a still-open point makes a theorem `conditional`
  (`status_deps`), also through the value of a Prop-valued definition;
* once the open points in `status_deps` are proved, the theorem is
  `proved` (cascade within one registry);
* open points in the conclusion do not make a theorem conditional;
* a name with both attributes is a single `open` entry;
* published definitions are `definition`, published axioms `axiom`;
* exact ids: nothing unresolved; an open point and a theorem stating
  its proposition share `stmt`; a theorem's `ref` is its `stmt`; the
  imported part of the cone is cached and a warm run reproduces the ids;
* `generateRegistryCore` rewrites files only when their content changes.
-/

open Lean CA.Registry

private def src : String := "
import CA
@[open_point \"nobody proves this here\"] def Open1 : Prop := ∀ n : Nat, n * 1 = n
@[open_point \"proved below\"] def Conj : Prop := ∀ n : Nat, n + 0 = n
@[publish] theorem conj_proof : Conj := fun n => Nat.add_zero n
@[publish] theorem conj_literal : ∀ n : Nat, n + 0 = n := fun n => Nat.add_zero n
@[publish] theorem uses_conj (h : Conj) : 1 + 0 = 1 := h 1
@[publish] theorem cond1 (h : Open1) : 2 * 1 = 2 := h 2
@[publish] def Wrap : Prop := Open1 ∧ True
@[publish] theorem uses_wrap (h : Wrap) : 2 * 1 = 2 := h.1 2
@[publish] theorem refut_shape : ¬ (Open1 ∧ False) := fun h => h.2
@[publish] theorem about : Open1 ∨ True := Or.inr trivial
@[open_point, publish \"both\"] def Both : Prop := ∀ n : Nat, n = n
@[publish] def notAProp : Nat := 3
@[publish] axiom ax : (1 : Nat) = 1
"

private unsafe def enableInitImpl : IO Unit := Lean.enableInitializersExecution
@[implemented_by enableInitImpl] private opaque enableInit : IO Unit

def main : IO UInt32 := do
  enableInit
  initSearchPath (← findSysroot)
  let some env ← Elab.runFrontend src {} "<registry-test>" `RegistryTest
    | IO.eprintln "registry-test: elaboration failed"; return 1
  let dir := ".lake/registry-test-out"
  if ← System.FilePath.pathExists dir then IO.FS.removeDirAll dir   -- a previous run must not mask the first write
  let cacheDir : System.FilePath := System.FilePath.mk (dir ++ "/cache")
  let t0 ← IO.monoMsNow
  let ids ← computeEntryIds env ((annotated env).map (·.1)) CA.SHA256.pureHasher (some cacheDir)
  let t1 ← IO.monoMsNow
  IO.println s!"exact ids: cone computed in {t1 - t0} ms (cold cache)"
  let entries := classify env ids
  let byName : Std.HashMap Name Entry := entries.foldl (fun m e => m.insert e.name e) {}
  let mut fails : Array String := #[]
  let check (label : String) (ok : Bool) : IO (Array String) := do
    IO.println s!"  {if ok then "✓" else "✗"} {label}"
    return if ok then #[] else #[label]
  let expect (n : Name) (st : Status) (proves provedBy deps : Array Name := #[]) : IO (Array String) := do
    match byName.get? n with
    | none => check s!"{n}: entry present" false
    | some e =>
      check s!"{n}: {st}{if proves.isEmpty then "" else s!", proves {proves}"}{if provedBy.isEmpty then "" else s!", proved_by {provedBy}"}{if deps.isEmpty then "" else s!", status_deps {deps}"}"
        (e.status == st && e.proves == proves && e.provedBy == provedBy && e.statusDeps == deps)

  IO.println "Classification:"
  fails := fails ++ (← check "13 entries, one per name" (entries.size == 13))
  fails := fails ++ (← expect `Open1 .«open»)
  fails := fails ++ (← expect `Conj .proved (provedBy := #[`conj_literal, `conj_proof]))
  fails := fails ++ (← expect `conj_proof .proved (proves := #[`Conj]))
  fails := fails ++ (← expect `conj_literal .proved (proves := #[`Conj]))
  fails := fails ++ (← expect `uses_conj .proved (deps := #[`Conj]))
  fails := fails ++ (← expect `cond1 .conditional (deps := #[`Open1]))
  fails := fails ++ (← expect `Wrap .definition)
  fails := fails ++ (← expect `uses_wrap .conditional (deps := #[`Open1]))
  fails := fails ++ (← expect `refut_shape .proved)
  fails := fails ++ (← expect `about .proved)
  fails := fails ++ (← expect `Both .«open»)
  fails := fails ++ (← check "Both: open point wins, publish description kept"
    ((byName.get? `Both).any fun e => e.isOpenPoint && e.description == "both"))
  fails := fails ++ (← expect `notAProp .definition)
  fails := fails ++ (← expect `ax .«axiom»)

  IO.println "Exact ids:"
  fails := fails ++ (← check "every entry has exact ids (nothing unresolved)"
    (entries.all fun e => e.unresolved.isEmpty))
  fails := fails ++ (← check "Conj (open point) and conj_literal share the exact statement id"
    (match byName.get? `Conj, byName.get? `conj_literal with
     | some a, some b => a.stmt == b.stmt
     | _, _ => false))
  fails := fails ++ (← check "conj_proof : Conj has a different stmt (it states the constant, not the proposition)"
    (match byName.get? `Conj, byName.get? `conj_proof with
     | some a, some b => a.stmt != b.stmt
     | _, _ => false))
  fails := fails ++ (← check "a theorem's ref is its stmt; a definition's is not"
    (match byName.get? `conj_literal, byName.get? `notAProp with
     | some t, some d => t.ref == t.stmt && d.ref != d.stmt
     | _, _ => false))
  let cacheFiles ← cacheDir.readDir
  fails := fails ++ (← check "the imported part of the cone was cached" (cacheFiles.size == 1))
  let t2 ← IO.monoMsNow
  let ids2 ← computeEntryIds env ((annotated env).map (·.1)) CA.SHA256.pureHasher (some cacheDir)
  let t3 ← IO.monoMsNow
  IO.println s!"exact ids: recomputed in {t3 - t2} ms (warm cache)"
  fails := fails ++ (← check "warm-cache ids equal cold-cache ids"
    (ids.toList.all fun (n, e) => match ids2.get? n with
      | some e' => e'.stmt == e.stmt && e'.ref == e.ref
      | none => false))

  IO.println "Generation:"
  let s1 ← generateRegistryCore env dir (project := "registry-test") (cacheDir := some cacheDir)
  fails := fails ++ (← check "summary counts"
    (s1.entries == 13 && s1.openPoints == 3 && s1.openProved == 1 && s1.published == 10 &&
     s1.proved == 5 && s1.conditional == 2 && s1.definitions == 2 && s1.axioms == 1))
  fails := fails ++ (← check "first generation writes" s1.changed)
  let s2 ← generateRegistryCore env dir (project := "registry-test") (cacheDir := some cacheDir)
  fails := fails ++ (← check "second generation leaves files untouched" (!s2.changed))
  let decls ← IO.FS.readFile s1.declsPath
  fails := fails ++ (← check "declarations.json parses and has 13 entries"
    (match Lean.Json.parse decls with
     | .ok (.arr a) => a.size == 13
     | _ => false))

  if fails.isEmpty then
    IO.println "\nAll Registry tests passed."
    return 0
  else
    IO.println s!"\n{fails.size} Registry test(s) FAILED: {fails}"
    return 1

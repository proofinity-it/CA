import Lean
import CA.ExprHash

open Lean
open CA.ExprHash

namespace CA.Export

/-! ## JSON Serialization -/

def DeclHash.toJson (d : DeclHash) : Lean.Json :=
  let fields : List (String × Lean.Json) := [
    ("name", .str d.name.toString),
    ("module", .str d.module.toString),
    ("kind", .str d.kind),
    ("type_hash", .str d.typeHash),
    ("pp_type", .str d.ppType),
    ("type_deps", .arr (d.typeDeps.map fun n => .str n.toString)),
    ("value_deps", .arr (d.valueDeps.map fun n => .str n.toString))
  ]
  let fields := match d.valueHash with
    | some vh => fields ++ [("value_hash", .str vh)]
    | none => fields
  .mkObj fields

/-- Build the full JSON manifest with metadata. -/
def manifestToJson (decls : Array DeclHash)
    (toolchain : String) (transparency : String) (hashMode : String) : Lean.Json :=
  .mkObj [
    ("lean_toolchain", .str toolchain),
    ("transparency", .str transparency),
    ("hash_mode", .str hashMode),
    ("total_declarations", .num ⟨decls.size, 0⟩),
    ("declarations", .arr (decls.map DeclHash.toJson))
  ]

/-- Write the JSON manifest to a file. -/
def writeManifest (path : String) (decls : Array DeclHash)
    (toolchain : String) (transparency : String) (hashMode : String) : IO Unit := do
  let manifest := manifestToJson decls toolchain transparency hashMode
  IO.FS.writeFile path manifest.pretty
  IO.eprintln s!"Wrote manifest to {path} ({decls.size} declarations)"

/-! ## Edge List Export -/

/-- Write the dependency edge list as TSV.
    Each line: `source_type_hash\ttarget_type_hash`
    Only includes edges where both source and target are in the hash map. -/
def writeEdgeList (path : String) (decls : Array DeclHash) : IO Unit := do
  -- Build name → typeHash mapping
  let mut hashMap : Std.HashMap Name String := {}
  for d in decls do
    hashMap := hashMap.insert d.name d.typeHash

  let mut lines : Array String := #["# source_type_hash\ttarget_type_hash"]
  let mut edgeCount : Nat := 0
  for d in decls do
    for dep in d.typeDeps do
      if let some depHash := hashMap.get? dep then
        lines := lines.push s!"{d.typeHash}\t{depHash}"
        edgeCount := edgeCount + 1

  let content := String.intercalate "\n" lines.toList
  IO.FS.writeFile path content
  IO.eprintln s!"Wrote edge list to {path} ({edgeCount} edges)"

/-! ## Summary Statistics -/

/-- Print summary statistics about the content-addressed declarations. -/
def printSummary (decls : Array DeclHash) : IO Unit := do
  let total := decls.size

  -- Count by kind
  let mut theorems := 0
  let mut definitions := 0
  let mut axioms := 0
  let mut other := 0
  for d in decls do
    match d.kind with
    | "theorem" => theorems := theorems + 1
    | "definition" => definitions := definitions + 1
    | "axiom" => axioms := axioms + 1
    | _ => other := other + 1

  -- Count distinct type hashes
  let mut typeHashes : Std.HashSet String := {}
  for d in decls do
    typeHashes := typeHashes.insert d.typeHash

  let distinctTypes := typeHashes.size
  let duplicateTypes := total - distinctTypes

  -- Find largest equivalence classes (type hash → count)
  let mut hashCounts : Std.HashMap String Nat := {}
  for d in decls do
    let prev := hashCounts.getD d.typeHash 0
    hashCounts := hashCounts.insert d.typeHash (prev + 1)

  let multiCounts := hashCounts.toList.filter fun (_, cnt) => cnt > 1
  let sortedMulti := multiCounts.toArray.qsort fun (_, a) (_, b) => a > b

  -- Hash frequency histogram
  let mut freq1 := 0
  let mut freq2to5 := 0
  let mut freq6to20 := 0
  let mut freq21plus := 0
  for (_, cnt) in hashCounts.toList do
    if cnt == 1 then freq1 := freq1 + 1
    else if cnt ≤ 5 then freq2to5 := freq2to5 + 1
    else if cnt ≤ 20 then freq6to20 := freq6to20 + 1
    else freq21plus := freq21plus + 1

  IO.eprintln s!"\nContent Address Summary"
  IO.eprintln (String.ofList (List.replicate 50 '='))
  IO.eprintln ""
  IO.eprintln s!"  Total declarations:     {total}"
  IO.eprintln s!"    theorems:             {theorems}"
  IO.eprintln s!"    definitions:          {definitions}"
  IO.eprintln s!"    axioms:               {axioms}"
  IO.eprintln s!"    other:                {other}"
  IO.eprintln ""
  IO.eprintln s!"  Distinct type hashes:   {distinctTypes}"
  IO.eprintln s!"  Duplicate types:        {duplicateTypes} ({total - distinctTypes} names share a hash with another)"
  IO.eprintln ""
  IO.eprintln s!"  Hash frequency distribution:"
  IO.eprintln s!"    unique (freq=1):      {freq1}"
  IO.eprintln s!"    freq 2-5:             {freq2to5}"
  IO.eprintln s!"    freq 6-20:            {freq6to20}"
  IO.eprintln s!"    freq 21+:             {freq21plus}"

  if !sortedMulti.isEmpty then
    IO.eprintln ""
    IO.eprintln s!"  Largest equivalence classes (same type hash):"
    let limit := min 10 sortedMulti.size
    for i in [:limit] do
      let (h, cnt) := sortedMulti[i]!
      -- Find names with this hash
      let names := decls.filter (fun d => d.typeHash == h) |>.map (fun d => d.name.toString)
      let namePreview := if names.size ≤ 3
        then String.intercalate ", " names.toList
        else String.intercalate ", " (names[:3].toArray.toList) ++ s!", ... (+{names.size - 3})"
      IO.eprintln s!"    [{cnt}] {h}: {namePreview}"

end CA.Export

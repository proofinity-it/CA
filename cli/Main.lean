import CA
import CaCli.SHA256FFI
import Lean
import Lean.Util.Path
import Cli
import RedisLean

open Lean Meta
open CA.Canonical
open CA.ExprHash
open CA.Export
open CA.Util
open Redis

/-- The CLI hashes with OpenSSL (same digests as the library's pure default). -/
def fastHasher : CA.SHA256.Hasher := CA.SHA256.FFI.hasher

-- Enable execution of plain `initialize` blocks when oleans are imported.
-- Without this, `importModules` in a compiled binary silently skips the
-- imported modules' initializers, so persistent extensions declared with
-- plain `initialize` (e.g. `CA.Registry`'s NameMapExtensions) never
-- restore their entries and `@[publish]`/`@[open_point]` annotations
-- read back as absent.
private unsafe def enableInitImpl : IO Unit := Lean.enableInitializersExecution
@[implemented_by enableInitImpl] private opaque enableInit : IO Unit

-- Declaration collection

def isInternalName (name : Name) : Bool :=
  name.isInternal ||
  let s := name.toString
  (s.splitOn "._").length > 1 || (s.splitOn "match_").length > 1 || (s.splitOn "_uniq").length > 1

def collectDeclarations (env : Environment) : Array (Name × ConstantInfo) := Id.run do
  let mut decls : Array (Name × ConstantInfo) := #[]
  for (name, ci) in env.constants.toList do
    if !isInternalName name then
      decls := decls.push (name, ci)
  return decls.qsort (fun (a, _) (b, _) => a.toString < b.toString)

-- Redis connection helper

def withRedis (action : RedisM α) : IO (Except Redis.Error α) :=
  runRedisNoState { config := {}, enableMetrics := false } action

-- Formatting helpers

def padRight (s : String) (width : Nat) : String :=
  s ++ String.ofList (List.replicate (width - min width s.length) ' ')

def padLeft (s : String) (width : Nat) : String :=
  String.ofList (List.replicate (width - min width s.length) ' ') ++ s

def truncate (s : String) (maxLen : Nat) : String :=
  if s.length > maxLen then (s.take (maxLen - 3)).toString ++ "..." else s

-- Shared helpers

private def moduleToRelPath (mod : Name) : System.FilePath :=
  match mod with
  | .str p s => moduleToRelPath p / s
  | .num p n => moduleToRelPath p / toString n
  | .anonymous => ⟨"."⟩

private def findModuleOLean (sp : System.SearchPath) (mod : Name) : IO (Option System.FilePath) := do
  let relPath := (moduleToRelPath mod).withExtension "olean"
  for dir in sp do
    let fullPath := dir / relPath
    if ← fullPath.pathExists then
      return some fullPath
  return none

private def addLakePackagePaths : IO Unit := do
  let packagesDir : System.FilePath := ".lake" / "packages"
  if ← packagesDir.pathExists then
    let entries ← packagesDir.readDir
    let sp ← searchPathRef.get
    let mut newPaths : List System.FilePath := []
    for entry in entries do
      let libDir := entry.path / ".lake" / "build" / "lib" / "lean"
      if ← libDir.pathExists then
        newPaths := libDir :: newPaths
    let ownLib : System.FilePath := ".lake" / "build" / "lib" / "lean"
    if ← ownLib.pathExists then
      newPaths := ownLib :: newPaths
    searchPathRef.set (newPaths ++ sp)

def loadDeclarations (moduleName : Name) (extraPath : Option String := none)
    : IO (Environment × Array (Name × ConstantInfo)) := do
  IO.eprintln s!"Loading environment for {moduleName}..."
  enableInit
  initSearchPath (← findSysroot)
  addLakePackagePaths
  if let some p := extraPath then
    let sp ← searchPathRef.get
    searchPathRef.set (p :: sp)
    IO.eprintln s!"Added search path: {p}"
  let sp ← searchPathRef.get
  let found ← findModuleOLean sp moduleName
  if found.isNone then
    IO.eprintln s!"error: Module '{moduleName}' not found — no .olean file in search path.\nIf using Mathlib, run 'lake exe cache get' first to download precompiled .olean files."
    IO.Process.exit 1
  -- `loadExts := true`: restore persistent env-extension state (the
  -- `@[publish]`/`@[open_point]` NameMapExtensions live there); the
  -- default skips it and every annotation would read back as absent.
  let env ← importModules #[{module := moduleName}] {} (loadExts := true)
  IO.eprintln s!"Environment loaded: {env.constants.toList.length} constants"
  let decls := collectDeclarations env
  IO.eprintln s!"Found {decls.size} declarations (excluding internal names)"
  return (env, decls)

def parseModuleName (p : Cli.Parsed) : Name :=
  if p.hasFlag "module"
  then (p.flag! "module" |>.as! String).toName
  else `Mathlib

def getExtraPath (p : Cli.Parsed) : Option String :=
  if p.hasFlag "path"
  then some (p.flag! "path" |>.as! String)
  else none

-- Redis key constants

def keyPrefix := "ca"
def declKey (name : String) : String := s!"{keyPrefix}:decl:{name}"
def addrKey (hex : String) : String := s!"{keyPrefix}:addr:{hex}"
def name2addrKey (name : String) : String := s!"{keyPrefix}:name2addr:{name}"
def addrNamesKey (hex : String) : String := s!"{keyPrefix}:addrnames:{hex}"
def metaKey : String := s!"{keyPrefix}:meta"
def allKey : String := s!"{keyPrefix}:all"
def kindKey (kind : String) : String := s!"{keyPrefix}:kind:{kind}"

-- Base64 Encoding/Decoding

private def base64Table : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

def base64Encode (data : ByteArray) : String := Id.run do
  let tbl := base64Table
  let n := data.size
  let mut result : Array Char := #[]
  let mut i := 0
  while i + 2 < n do
    let b0 := data[i]!.toNat
    let b1 := data[i+1]!.toNat
    let b2 := data[i+2]!.toNat
    result := result.push tbl[b0 >>> 2]!
    result := result.push tbl[((b0 &&& 3) <<< 4) ||| (b1 >>> 4)]!
    result := result.push tbl[((b1 &&& 15) <<< 2) ||| (b2 >>> 6)]!
    result := result.push tbl[b2 &&& 63]!
    i := i + 3
  let rem := n - i
  if rem == 1 then
    let b0 := data[i]!.toNat
    result := result.push tbl[b0 >>> 2]!
    result := result.push tbl[(b0 &&& 3) <<< 4]!
    result := result.push '='
    result := result.push '='
  else if rem == 2 then
    let b0 := data[i]!.toNat
    let b1 := data[i+1]!.toNat
    result := result.push tbl[b0 >>> 2]!
    result := result.push tbl[((b0 &&& 3) <<< 4) ||| (b1 >>> 4)]!
    result := result.push tbl[(b1 &&& 15) <<< 2]!
    result := result.push '='
  return String.ofList result.toList

private def base64DecodeChar (c : Char) : Nat :=
  if 'A' ≤ c && c ≤ 'Z' then c.toNat - 'A'.toNat
  else if 'a' ≤ c && c ≤ 'z' then c.toNat - 'a'.toNat + 26
  else if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat + 52
  else if c == '+' then 62
  else if c == '/' then 63
  else 0

def base64Decode (s : String) : ByteArray := Id.run do
  let chars := s.toList.filter (· != '=')
  let n := chars.length
  let mut result : ByteArray := .empty
  let arr := chars.toArray
  let mut i := 0
  while i + 3 < n do
    let a := base64DecodeChar arr[i]!
    let b := base64DecodeChar arr[i+1]!
    let c := base64DecodeChar arr[i+2]!
    let d := base64DecodeChar arr[i+3]!
    result := result.push ((a <<< 2 ||| b >>> 4) % 256).toUInt8
    result := result.push (((b &&& 15) <<< 4 ||| c >>> 2) % 256).toUInt8
    result := result.push (((c &&& 3) <<< 6 ||| d) % 256).toUInt8
    i := i + 4
  let rem := n - i
  if rem >= 2 then
    let a := base64DecodeChar arr[i]!
    let b := base64DecodeChar arr[i+1]!
    result := result.push ((a <<< 2 ||| b >>> 4) % 256).toUInt8
    if rem >= 3 then
      let c := base64DecodeChar arr[i+2]!
      result := result.push (((b &&& 15) <<< 4 ||| c >>> 2) % 256).toUInt8
  return result

-- Redis address operations

structure AddrEntry where
  name      : String
  module    : String
  kind      : String
  ppType    : String
  typeBytes : ByteArray

def storeDecl (name kind ppType : String) : RedisM Unit := do
  let key := declKey name
  discard $ hset key "name" name
  discard $ hset key "kind" kind
  discard $ hset key "type" ppType
  discard $ sadd allKey name
  discard $ sadd (kindKey kind) name

def storeAddress (name : String) (typeHash : String)
    (valueHash : Option String) (typeDeps valueDeps : Array String) : RedisM Unit := do
  let key := declKey name
  discard $ hset key "addr_type" typeHash
  match valueHash with
  | some vh => discard $ hset key "addr_value" vh
  | none => pure ()
  discard $ hset key "addr_type_deps" (String.intercalate "," typeDeps.toList)
  discard $ hset key "addr_value_deps" (String.intercalate "," valueDeps.toList)

def storeAddrIndex (name : String) (typeHash : String) (module kind ppType : String)
    (typeBytes : ByteArray) : RedisM Unit := do
  let ak := addrKey typeHash
  discard $ hset ak "name" name
  discard $ hset ak "module" module
  discard $ hset ak "kind" kind
  discard $ hset ak "pp_type" ppType
  discard $ hset ak "type_bytes" (base64Encode typeBytes)
  discard $ set (name2addrKey name) typeHash
  discard $ sadd (addrNamesKey typeHash) name

def lookupByAddr (hex : String) : RedisM (Option AddrEntry) := do
  let ak := addrKey hex
  let nameBytes ← hget ak "name"
  let name := String.fromUTF8! nameBytes
  if name.isEmpty then return none
  let module := String.fromUTF8! (← hget ak "module")
  let kind := String.fromUTF8! (← hget ak "kind")
  let ppType := String.fromUTF8! (← hget ak "pp_type")
  let tbStr := String.fromUTF8! (← hget ak "type_bytes")
  let typeBytes := base64Decode tbStr
  return some { name, module, kind, ppType, typeBytes }

def lookupByName (name : String) : RedisM (Option AddrEntry) := do
  let hexBytes ← get (name2addrKey name)
  let hex := String.fromUTF8! hexBytes
  if hex.isEmpty then return none
  lookupByAddr hex

def lookupHashByName (name : String) : RedisM (Option String) := do
  let hexBytes ← get (name2addrKey name)
  let hex := String.fromUTF8! hexBytes
  if hex.isEmpty then return none
  return some hex

def clearAll : RedisM Unit := do
  let existingKeys ← keys (α := String) s!"{keyPrefix}:*".toUTF8
  if !existingKeys.isEmpty then
    let keyStrings := existingKeys.map String.fromUTF8!
    discard $ del keyStrings

-- Subcommand: fetch

def runFetchCmd (p : Cli.Parsed) : IO UInt32 := do
  let moduleName := parseModuleName p
  let levelStr := if p.hasFlag "level"
    then p.flag! "level" |>.as! String
    else "0"
  let level := if levelStr == "1" then CanonLevel.l1 else CanonLevel.l0
  let (env, allDecls) ← loadDeclarations moduleName (getExtraPath p)
  let decls := if p.hasFlag "theorems"
    then allDecls.filter fun (_, ci) => match ci with | .thmInfo _ => true | _ => false
    else allDecls
  if p.hasFlag "theorems" then
    IO.eprintln s!"Filtered to {decls.size} theorems (out of {allDecls.size} declarations)"

  IO.eprintln s!"Computing content addresses (level={levelStr})..."
  let hashes ← computeNameBasedHashes env decls level (hasher := fastHasher)

  IO.eprintln "Connecting to Redis..."
  let result ← withRedis do
    clearAll
    IO.eprintln s!"Cleared existing {keyPrefix}:* keys"

    let mut count : Nat := 0
    for dh in hashes do
      let nameStr := dh.name.toString
      storeDecl nameStr dh.kind dh.ppType
      let typeDeps := dh.typeDeps.map (·.toString)
      let valueDeps := dh.valueDeps.map (·.toString)
      storeAddress nameStr dh.typeHash dh.valueHash typeDeps valueDeps
      storeAddrIndex nameStr dh.typeHash dh.module.toString dh.kind dh.ppType dh.typeBytes
      count := count + 1
      if count % 1000 == 0 then
        IO.eprintln s!"Progress: {count} declarations stored..."

    discard $ hset metaKey "count" (toString count)
    discard $ hset metaKey "module" (toString moduleName)
    discard $ hset metaKey "level" levelStr
    return count

  match result with
  | .ok count =>
    IO.eprintln s!"Registered {count} declarations in Redis (with addresses)"
    return 0
  | .error e =>
    IO.eprintln s!"Redis error: {e}"
    return 1

def fetchCmd : Cli.Cmd := `[Cli|
  fetch VIA runFetchCmd; ["0.1.0"]
  "Load Mathlib environment, compute content addresses, and store everything in Redis."

  FLAGS:
    m, module : String; "Module to load (default: Mathlib)"
    p, path : String; "Extra search path for .olean files (e.g. /path/to/mathlib4/.lake/build/lib)"
    level : String; "Normalization level: 0 or 1 (default: 0)"
    theorems; "Only index theorems (skip definitions, axioms, etc.)"
]

-- Subcommand: address

def runAddressCmd (p : Cli.Parsed) : IO UInt32 := do
  let moduleName := parseModuleName p
  let levelStr := if p.hasFlag "level"
    then p.flag! "level" |>.as! String
    else "0"
  let outputPath := if p.hasFlag "output"
    then p.flag! "output" |>.as! String
    else "manifest.json"
  let edgesPath := if p.hasFlag "edges"
    then some (p.flag! "edges" |>.as! String)
    else none

  let level := if levelStr == "1" then CanonLevel.l1 else CanonLevel.l0

  -- Single-declaration lookup
  if p.hasFlag "name" then
    let nameStr := p.flag! "name" |>.as! String
    let recompute := p.hasFlag "recompute"

    -- Try Redis first (instant) unless --recompute is passed
    if !recompute then
      let result ← withRedis (lookupByName nameStr)
      match result with
      | .ok (some entry) =>
        let hashResult ← withRedis (lookupHashByName nameStr)
        let hash := match hashResult with
          | .ok (some h) => h
          | _ => "(unknown)"
        IO.eprintln s!"\n{nameStr}"
        IO.eprintln s!"  Kind:        {entry.kind}"
        IO.eprintln s!"  Module:      {entry.module}"
        IO.eprintln s!"  Type addr:   {hash}"
        IO.eprintln s!"  Type:        {entry.ppType}"
        return 0
      | _ => IO.eprintln "Not found in Redis, falling back to environment..."

    let name := nameStr.toName
    let (env, _) ← loadDeclarations moduleName (getExtraPath p)

    match env.find? name with
    | none =>
      IO.eprintln s!"Declaration not found: {name}"
      return 1
    | some ci =>
      let decls : Array (Name × ConstantInfo) := #[(name, ci)]
      IO.eprintln s!"Computing address for {name} (level={levelStr})..."
      let hashes ← computeNameBasedHashes env decls level (hasher := fastHasher)

      match hashes[0]? with
      | none =>
        IO.eprintln s!"Failed to compute address for {name}"
        return 1
      | some dh =>
        IO.eprintln s!"\n{name}"
        IO.eprintln s!"  Kind:        {dh.kind}"
        IO.eprintln s!"  Type addr:   {dh.typeHash}"
        match dh.valueHash with
        | some vh => IO.eprintln s!"  Value addr:  {vh}"
        | none => pure ()
        IO.eprintln s!"  Type deps:   {dh.typeDeps.size}"
        IO.eprintln s!"  Value deps:  {dh.valueDeps.size}"

        -- Sink to Redis
        let nameStr := dh.name.toString
        let result ← withRedis do
          storeAddress nameStr dh.typeHash dh.valueHash
            (dh.typeDeps.map (·.toString)) (dh.valueDeps.map (·.toString))
          storeAddrIndex nameStr dh.typeHash dh.module.toString dh.kind dh.ppType dh.typeBytes
        match result with
        | .ok _ => pure ()
        | .error e => IO.eprintln s!"Redis error: {e}"

        return 0

  -- Batch mode
  let (env, decls) ← loadDeclarations moduleName (getExtraPath p)

  IO.eprintln s!"Computing addresses (level={levelStr})..."

  let hashes ← computeNameBasedHashes env decls level (hasher := fastHasher)

  let transparency := if level == .l0 then "none" else "reducible"
  let hashModeStr := "name_based"

  let toolchain ← IO.FS.readFile "lean-toolchain" <&> (·.trimAscii.toString)
  writeManifest outputPath hashes toolchain transparency hashModeStr

  if let some ep := edgesPath then
    writeEdgeList ep hashes

  printSummary hashes

  -- Sink to Redis
  IO.eprintln "Storing addresses to Redis..."
  let result ← withRedis do
    for dh in hashes do
      let nameStr := dh.name.toString
      let typeDeps := dh.typeDeps.map (·.toString)
      let valueDeps := dh.valueDeps.map (·.toString)
      storeAddress nameStr dh.typeHash dh.valueHash typeDeps valueDeps
      storeAddrIndex nameStr dh.typeHash dh.module.toString dh.kind dh.ppType dh.typeBytes
  match result with
  | .ok _ => IO.eprintln s!"Stored addresses for {hashes.size} declarations in Redis"
  | .error e => IO.eprintln s!"Redis error: {e}"

  return 0

def addressCmd : Cli.Cmd := `[Cli|
  address VIA runAddressCmd; ["0.1.0"]
  "Compute content addresses for all declarations and export manifest."

  FLAGS:
    m, module : String; "Module to load (default: Mathlib)"
    p, path : String; "Extra search path for .olean files"
    n, name : String; "Compute address for a single declaration"
    level : String; "Normalization level: 0 (universe renaming) or 1 (reducible normalization). Default: 0"
    output : String; "Output JSON manifest path (default: manifest.json)"
    edges : String; "Output edge list TSV path (optional)"
    recompute; "Force recomputation from environment (skip Redis lookup)"
]

-- Subcommand: registry

def runRegistryCmd (p : Cli.Parsed) : IO UInt32 := do
  let moduleName := parseModuleName p
  let outputDir := if p.hasFlag "output"
    then p.flag! "output" |>.as! String
    else "registry"

  let (env, _) ← loadDeclarations moduleName (getExtraPath p)

  let openPoints := CA.Registry.getOpenPoints env
  let published := CA.Registry.getPublished env
  IO.eprintln s!"Found {openPoints.length} open points, {published.length} published"

  -- Same generation core as the `#ca_registry` command: both paths must
  -- produce byte-identical registries.
  let toolchain ← try
      pure (some (← IO.FS.readFile "lean-toolchain").trimAscii.toString)
    catch _ => pure none
  let s ← CA.Registry.generateRegistryCore env outputDir
    (project := moduleName.toString) (toolchain := toolchain) (hasher := fastHasher)
  IO.eprintln s!"{if s.changed then "Wrote" else "Unchanged"} {s.declsPath} ({s.entries} entries), {s.metaPath}"
  IO.eprintln s!"Summary: {s.openPoints} open points ({s.openProved} proved), {s.published} published: {s.proved} proved, {s.conditional} conditional, {s.definitions} definitions, {s.axioms} axioms"
  return 0

def registryCmd : Cli.Cmd := `[Cli|
  registry VIA runRegistryCmd; ["0.1.0"]
  "Generate a project registry from @[publish] and @[open_point] annotations."

  FLAGS:
    m, module : String; "Module to load (default: Mathlib)"
    p, path : String; "Extra search path for .olean files"
    o, output : String; "Output directory (default: registry)"
]

-- Subcommand: selftest

/-- Cross-check the OpenSSL hasher against the library's pure SHA-256 and
    the FIPS 180-4 `"abc"` vector. Ids must not depend on the hasher. -/
def runSelftestCmd (_ : Cli.Parsed) : IO UInt32 := do
  let vectors : Array ByteArray := #[
    ByteArray.empty, "abc".toUTF8,
    "The quick brown fox jumps over the lazy dog".toUTF8,
    ByteArray.mk (Array.range 55 |>.map (·.toUInt8)),      -- one block, max payload
    ByteArray.mk (Array.range 56 |>.map (·.toUInt8)),      -- forces a second block
    ByteArray.mk (Array.range 1000 |>.map (·.toUInt8)),
    ByteArray.mk (Array.range 100000 |>.map (·.toUInt8))]
  let mut ok := true
  for v in vectors do
    if (← fastHasher v) != CA.SHA256.sha256Pure v then
      ok := false
      IO.eprintln s!"selftest: OpenSSL and sha256Pure disagree on a {v.size}-byte input"
  let abc := CA.SHA256.toHex256 (← fastHasher "abc".toUTF8)
  if abc != "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" then
    ok := false
    IO.eprintln s!"selftest: sha256(\"abc\") = {abc}, not the FIPS vector"
  if ok then
    IO.println s!"selftest ok: OpenSSL sha256 and sha256Pure agree on {vectors.size} vectors; FIPS vector matches"
    return 0
  else
    return 1

def selftestCmd : Cli.Cmd := `[Cli|
  selftest VIA runSelftestCmd; ["0.1.0"]
  "Check that the OpenSSL SHA-256 agrees with the library's pure implementation."
]

-- Top-level CLI

def caCmd : Cli.Cmd := `[Cli|
  ca NOOP; ["0.1.0"]
  "Content-addressed declaration hashing for Lean 4 environments."

  SUBCOMMANDS:
    fetchCmd;
    addressCmd;
    registryCmd;
    selftestCmd
]

def main (args : List String) : IO UInt32 :=
  caCmd.validate args

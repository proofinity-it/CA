import CA
import CaCli.SHA256FFI
import CaNodeFile
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
  -- Report an import failure ourselves: an uncaught IO error from here
  -- crashed in the runtime's own error printer (SIGSEGV) instead of
  -- showing the message.
  let env ← try importModules #[{module := moduleName}] {} (loadExts := true)
    catch e =>
      IO.eprintln s!"error: importing {moduleName}: {e}"
      IO.Process.exit 1
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
  fetch VIA runFetchCmd; ["0.3.0"]
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
  address VIA runAddressCmd; ["0.3.0"]
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
  registry VIA runRegistryCmd; ["0.3.0"]
  "Generate a project registry from @[publish] and @[open_point] annotations."

  FLAGS:
    m, module : String; "Module to load (default: Mathlib)"
    p, path : String; "Extra search path for .olean files"
    o, output : String; "Output directory (default: registry)"
]

/-- Read a 32-byte seed written by `ca keygen` (64 hex digits). -/
def readSeed (path : System.FilePath) : IO ByteArray := do
  let txt := (← IO.FS.readFile path).trimAscii.toString
  let cs := txt.toList.toArray
  unless cs.size == 64 && cs.all (fun c => c.isDigit || ('a' ≤ c.toLower && c.toLower ≤ 'f')) do
    throw (IO.userError s!"{path}: not a key file written by `ca keygen`")
  let v (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
  let mut b := ByteArray.empty
  for i in [:32] do b := b.push (v cs[2*i]! * 16 + v cs[2*i+1]!).toUInt8
  return b

-- Subcommands: pack, check (the node file)

def runPackCmd (p : Cli.Parsed) : IO UInt32 := do
  let moduleName := parseModuleName p
  let output := if p.hasFlag "output" then p.flag! "output" |>.as! String else "node.sqlite"
  let withProofs := !p.hasFlag "no-proofs"
  let (env, _) ← loadDeclarations moduleName (getExtraPath p)
  let roots : Array Name ←
    if p.hasFlag "all" then
      pure (env.constants.toList.toArray.map (·.1))
    else if p.hasFlag "own" then
      let pfx := moduleName
      pure <| (env.constants.toList.toArray.filter fun (n, _) =>
        match env.getModuleIdxFor? n with
        | some i => match env.header.moduleNames[i.toNat]? with
          | some m => pfx.isPrefixOf m
          | none => false
        | none => true).map (·.1)
    else
      let ann := CA.Registry.annotated env
      if ann.isEmpty then
        IO.eprintln "error: no @[publish] / @[open_point] declarations; use --own (this module's declarations) or --all"
        return 1
      pure (ann.map (·.1))
  let roots := roots.qsort Name.lt
  IO.eprintln s!"Packing {roots.size} root declarations ({if withProofs then "with proofs" else "statement mode"})..."
  let toolchain ← try
      pure (some (← IO.FS.readFile "lean-toolchain").trimAscii.toString)
    catch _ => pure none
  let info := #[("payload_format", toString CA.Payload.formatVersion.toNat),
                ("ca_scheme_version", toString CA.schemeVersion),
                ("node", "static"), ("project", moduleName.toString),
                ("proofs", if withProofs then "yes" else "no"),
                ("lean_toolchain", toolchain.getD Lean.versionString)]
  let t0 ← IO.monoMsNow
  let (node, rep) ← CA.Node.packEnvironment env roots withProofs fastHasher (info := info)
    (selfCheck := !p.hasFlag "fast") (withDeps := p.hasFlag "deps")
  let node ← if p.hasFlag "sign" then do
      let seed ← readSeed (p.flag! "sign" |>.as! String)
      let label := if p.hasFlag "label" then p.flag! "label" |>.as! String else moduleName.toString
      let n := CA.Node.bindEntries node seed label
      IO.eprintln s!"  {n.bindings.size} bindings in {label}@{CA.Node.keyText (CA.Ed25519.publicKey seed)}"
      pure n
    else pure node
  let t1 ← IO.monoMsNow
  CA.NodeFile.writeNode output node
  let size := (← System.FilePath.metadata output).byteSize
  IO.eprintln s!"Wrote {output}: {rep.declarations} declarations in {rep.units} units, {rep.statements} registry statements; {node.table.refs.size} refs, {node.table.names.size} names; {size} bytes ({(t1 - t0) / 1000} s)"
  if rep.unresolved > 0 then
    IO.eprintln s!"  {rep.unresolved} references hashed by name (spec.md §10): those ids are not exact"
  unless rep.inexact.isEmpty do
    IO.eprintln s!"  {rep.inexact.size} members do not rebuild exactly: {rep.inexact.toList.take 5}"
  for e in rep.errors.toList.take 20 do IO.eprintln s!"  error: {e}"
  return if rep.errors.isEmpty then 0 else 1

def packCmd : Cli.Cmd := `[Cli|
  pack VIA runPackCmd; ["0.3.0"]
  "Write a registry node file (SQLite, docs/payload.md): units, decorations, statements."

  FLAGS:
    m, module : String; "Module to load (default: Mathlib)"
    p, path : String; "Extra search path for .olean files"
    o, output : String; "Output file (default: node.sqlite)"
    own; "Pack every declaration of the module and its submodules (default: the @[publish] / @[open_point] ones)"
    all; "Pack every declaration of the loaded environment"
    "no-proofs"; "Statement mode: theorems without their proofs"
    sign : String; "Key file from `ca keygen`: claim the namespace LABEL@key and bind every entry's name in it"
    label : String; "Namespace label for --sign (default: the module name)"
    fast; "Skip the encoder's self-check (rebuilding every unit from its own output)"
    deps; "Also write the deps table (each declaration's references by ref id; derivable from the units, large)"
]

def runCheckCmd (p : Cli.Parsed) : IO UInt32 := do
  let path := p.positionalArg! "file" |>.as! String
  let t0 ← IO.monoMsNow
  let node ← CA.NodeFile.readNode path
  let rep ← CA.Node.checkNode node fastHasher
  let t1 ← IO.monoMsNow
  for (k, v) in node.info do IO.println s!"  {k}: {v}"
  IO.println s!"{path}: {rep.units} units, {rep.members} members, {rep.decorations} decorations checked in {(t1 - t0) / 1000} s"
  IO.println s!"  ids recomputed from the units' bytes; {rep.rebuilt} members rebuilt from their decorations to the same ids"
  IO.println s!"  naming variants: {rep.namingVariants} keys; inexact units (names hashed by name): {rep.inexact}"
  if rep.faults.isEmpty then
    IO.println "  no faults"
    return 0
  IO.println s!"  {rep.faults.size} FAULTS:"
  for f in rep.faults.toList.take 50 do IO.println s!"    {f}"
  return 1

def checkCmd : Cli.Cmd := `[Cli|
  check VIA runCheckCmd; ["0.3.0"]
  "Check a node file: every unit's ids recomputed from its bytes, every row against its unit, every decoration rebuilt."

  ARGS:
    file : String; "The node file (SQLite)"
]

-- Subcommands: merge, digest, diff (registry-protocol.md §6, §10)

def runMergeCmd (p : Cli.Parsed) : IO UInt32 := do
  let out : System.FilePath := p.positionalArg! "out" |>.as! String
  let inputs := p.variableArgsAs! String
  if inputs.size < 1 then IO.eprintln "error: nothing to merge"; return 1
  let mut node ← CA.NodeFile.readNode inputs[0]!
  let mut errors : Array String := #[]
  for path in inputs[1:] do
    let (m, errs) ← CA.Node.merge node (← CA.NodeFile.readNode path) fastHasher
    node := m; errors := errors ++ errs
  let rep ← CA.Node.checkNode node fastHasher
  if !errors.isEmpty || !rep.faults.isEmpty then
    IO.eprintln s!"error: the merge has {errors.size + rep.faults.size} faults; nothing written"
    for e in (errors ++ rep.faults).toList.take 20 do IO.eprintln s!"  {e}"
    return 1
  CA.NodeFile.writeNode out node
  IO.println s!"Wrote {out}: {node.units.size} units, {node.declarations.size} declarations, {node.entries.size} entries, {node.records.size} records, {node.bindings.size} bindings from {inputs.size} nodes; checked, no faults"
  return 0

def mergeCmd : Cli.Cmd := `[Cli|
  merge VIA runMergeCmd; ["0.3.0"]
  "Union of node files into one, re-encoded against one ref table and checked (ids unchanged; bindings: highest seq wins)."

  ARGS:
    out : String; "The merged node file to write"
    ...inputs : String; "Node files to merge"
]

def runDigestCmd (p : Cli.Parsed) : IO UInt32 := do
  let path := p.positionalArg! "file" |>.as! String
  let bits := if p.hasFlag "bits" then p.flag! "bits" |>.as! Nat else 8
  let node ← CA.NodeFile.readNode path
  let ds ← CA.Node.rangeDigests node bits fastHasher
  let j : Lean.Json := .mkObj [("bits", bits), ("keys", (CA.Node.contentKeys node).size),
    ("buckets", .arr (ds.map fun (c, d, n) => .mkObj [("bucket", c), ("digest", CA.SHA256.toHex256 d), ("count", n)]))]
  IO.println j.pretty
  return 0

def digestCmd : Cli.Cmd := `[Cli|
  digest VIA runDigestCmd; ["0.3.0"]
  "Range digests of a node's content keys: one SHA-256 per id-prefix bucket, for reconciliation."

  FLAGS:
    bits : Nat; "Prefix bits per bucket (default 8: up to 256 buckets)"

  ARGS:
    file : String; "The node file"
]

def runDiffCmd (p : Cli.Parsed) : IO UInt32 := do
  let a := p.positionalArg! "a" |>.as! String
  let b := p.positionalArg! "b" |>.as! String
  let bits := if p.hasFlag "bits" then p.flag! "bits" |>.as! Nat else 8
  let na ← CA.NodeFile.readNode a
  let nb ← CA.NodeFile.readNode b
  let (onlyA, onlyB, buckets, opened) ← CA.Node.diff na nb bits fastHasher
  IO.println s!"{buckets} bucket digests compared, {opened} opened; {onlyA.size} keys only in {a}, {onlyB.size} only in {b}"
  let nameOf (n : CA.Node.Node) : Std.HashMap ByteArray Name :=
    n.members.foldl (fun m r => if m.contains r.decl then m else m.insert r.decl r.name) {}
  let la := nameOf na
  let lb := nameOf nb
  for k in onlyA.toList.take 50 do IO.println s!"  - {CA.RefHash.toB58 k}{match la.get? k with | some n => s!"  {n}" | none => ""}"
  for k in onlyB.toList.take 50 do IO.println s!"  + {CA.RefHash.toB58 k}{match lb.get? k with | some n => s!"  {n}" | none => ""}"
  return if onlyA.isEmpty && onlyB.isEmpty then 0 else 2

def diffCmd : Cli.Cmd := `[Cli|
  diff VIA runDiffCmd; ["0.3.0"]
  "What two node files hold that the other lacks, found through range digests. Exit 2 when they differ."

  FLAGS:
    bits : Nat; "Prefix bits per bucket (default 8)"

  ARGS:
    a : String; "A node file"
    b : String; "Another node file"
]

-- Subcommand: migrate (two nodes, usually two toolchains: what survived)

def runMigrateCmd (p : Cli.Parsed) : IO UInt32 := do
  let a := p.positionalArg! "a" |>.as! String
  let b := p.positionalArg! "b" |>.as! String
  let na ← CA.NodeFile.readNode a
  let nb ← CA.NodeFile.readNode b
  let tc (n : CA.Node.Node) := (n.info.find? (·.1 == "lean_toolchain")).map (·.2) |>.getD "?"
  -- Declarations by name: did stmt, ref, decl survive?
  let byName (n : CA.Node.Node) : Std.HashMap Name CA.Node.DeclRow := Id.run do
    let rows : Std.HashMap ByteArray CA.Node.DeclRow := n.declarations.foldl (fun m d => m.insert d.decl d) {}
    let mut out := {}
    for m in n.members do
      if let some d := rows.get? m.decl then out := out.insert m.name d
    return out
  let da := byName na
  let db := byName nb
  let mut common := 0; let mut sameStmt := 0; let mut sameRef := 0; let mut sameDecl := 0
  let mut thm := 0; let mut thmSameStmt := 0
  let mut changed : Array Name := #[]
  for (n, d) in da.toArray do
    let some e := db.get? n | continue
    common := common + 1
    if d.stmt == e.stmt then sameStmt := sameStmt + 1 else changed := changed.push n
    if d.ref == e.ref then sameRef := sameRef + 1
    if d.decl == e.decl then sameDecl := sameDecl + 1
    if d.kind == "theorem" then
      thm := thm + 1
      if d.stmt == e.stmt then thmSameStmt := thmSameStmt + 1
  let onlyA := da.size - common
  let onlyB := db.size - common
  -- Entries: pair by type_hash (coarse), confirm by stmt (exact).
  let eb : Std.HashMap String (Array CA.Node.EntryRow) :=
    nb.entries.foldl (fun m e => m.insert e.typeHash ((m.getD e.typeHash #[]).push e)) {}
  let mut survived := 0; let mut moved : Array (Name × Array Name) := #[]; let mut gone : Array Name := #[]
  for e in na.entries do
    match eb.get? e.typeHash with
    | none => gone := gone.push e.name
    | some cands =>
      if cands.any (·.stmt == e.stmt) then survived := survived + 1
      else moved := moved.push (e.name, cands.map (·.name))
  let pct (x y : Nat) : String := if y == 0 then "-" else s!"{x * 1000 / y / 10}.{x * 1000 / y % 10}%"
  IO.println s!"{a} ({tc na}) → {b} ({tc nb})"
  IO.println s!"  declarations by name: {common} in both, {onlyA} only in the first, {onlyB} only in the second"
  IO.println s!"    stmt unchanged: {sameStmt} ({pct sameStmt common}); theorems: {thmSameStmt}/{thm} ({pct thmSameStmt thm})"
  IO.println s!"    ref unchanged:  {sameRef} ({pct sameRef common});  decl unchanged: {sameDecl} ({pct sameDecl common})"
  IO.println s!"  entries by type_hash: {survived} survived (same stmt), {moved.size} coarse matches whose stmt changed (candidates to confirm), {gone.size} with no coarse match"
  for n in changed.toList.take 20 do IO.println s!"    stmt changed: {n}"
  for (n, cs) in moved.toList.take 20 do IO.println s!"    candidate: {n} ~ {cs}"
  for n in gone.toList.take 20 do IO.println s!"    gone: {n}"
  return 0

def migrateCmd : Cli.Cmd := `[Cli|
  migrate VIA runMigrateCmd; ["0.3.0"]
  "Compare two nodes (two toolchains, two revisions): which statements survived by name, by stmt, by type_hash."

  ARGS:
    a : String; "The older node file"
    b : String; "The newer node file"
]

-- Keys (CA.Ed25519, pure Lean): `ca keygen`, `--sign KEYFILE`

def runKeygenCmd (p : Cli.Parsed) : IO UInt32 := do
  let path : System.FilePath := p.positionalArg! "file" |>.as! String
  if ← path.pathExists then
    IO.eprintln s!"error: {path} exists; not overwriting a key"
    return 1
  let seed ← CA.Ed25519.randomSeed
  IO.FS.writeFile path (CA.SHA256.toHex256 seed ++ "\n")
  IO.setAccessRights path { user := { read := true, write := true } }
  IO.println s!"{CA.Node.keyText (CA.Ed25519.publicKey seed)}"
  IO.eprintln s!"secret key written to {path} (keep it private); the line above is the public key, as used in namespace ids and record signers"
  return 0

def keygenCmd : Cli.Cmd := `[Cli|
  keygen VIA runKeygenCmd; ["0.3.0"]
  "Generate an Ed25519 key for signing records and bindings; prints the public key."

  ARGS:
    file : String; "Where to write the secret key (not overwritten)"
]

-- Subcommand: verify (CA.Verify: the kernel's verdict on a node)

def runVerifyCmd (p : Cli.Parsed) : IO UInt32 := do
  let path := p.positionalArg! "file" |>.as! String
  let imports : Array Name :=
    if p.hasFlag "import" then (p.flag! "import" |>.as! (Array String)).map String.toName else #[`Init]
  enableInit
  initSearchPath (← findSysroot)
  addLakePackagePaths
  let node ← CA.NodeFile.readNode path
  let fileToolchain := (node.info.find? (·.1 == "lean_toolchain")).map (·.2)
  if let some t := fileToolchain then
    if t != s!"leanprover/lean4:{Lean.versionString}" && !t.endsWith Lean.versionString then
      IO.eprintln s!"warning: the file was built on {t}; this ca runs Lean {Lean.versionString}"
  let env ← try importModules (imports.map fun m => { module := m }) {} (loadExts := false)
    catch e => IO.eprintln s!"error: importing {imports}: {e}"; IO.Process.exit 1
  let t0 ← IO.monoMsNow
  let (_, rep) ← CA.Verify.verifyNode env node fastHasher
  let t1 ← IO.monoMsNow
  IO.println s!"{path}: {rep.added} declarations added and accepted by the kernel, {rep.generated} recursors produced by it, {rep.present} already in the environment ({(t1 - t0) / 1000} s)"
  IO.println s!"  {rep.records.size} records: {(rep.records.filter (·.valid)).size} valid, {(rep.records.filter (!·.valid)).size} invalid (sorryAx)"
  unless rep.assumed.isEmpty do
    IO.println s!"  {rep.assumed.size} statements assumed as axioms:"
    for (n, r) in rep.assumed.toList.take 20 do IO.println s!"    {n}  {CA.RefHash.toB58 r}"
  if p.hasFlag "write" then
    let toolchain := fileToolchain.getD s!"leanprover/lean4:{Lean.versionString}"
    let seed ← if p.hasFlag "sign" then some <$> readSeed (p.flag! "sign" |>.as! String) else pure none
    let rows ← CA.Node.recordRows (rep.records.map fun r => (r.decl, r.valid, r.toJson toolchain)) seed fastHasher
    CA.NodeFile.appendRecords path rows
    IO.println s!"  {rows.size} records written to {path} ({match seed with | some s => s!"signed by {CA.Node.keyText (CA.Ed25519.publicKey s)}" | none => "unsigned"})"
  if rep.faults.isEmpty then
    IO.println "  no faults"
    return 0
  IO.println s!"  {rep.faults.size} FAULTS:"
  for f in rep.faults.toList.take 50 do IO.println s!"    {f}"
  return 1

def verifyCmd : Cli.Cmd := `[Cli|
  verify VIA runVerifyCmd; ["0.3.0"]
  "Rebuild every declaration of a node file and let the kernel judge it; one verification record per accepted theorem."

  FLAGS:
    "import" : Array String; "Modules to import first, the file's foundations (default: Init)"
    write; "Write the records into the file"
    sign : String; "Key file from `ca keygen`: sign the records written"

  ARGS:
    file : String; "The node file (SQLite)"
]

-- Subcommands: lookup, fetch-sources (the sources list, CA.Sources)

private def b58 (b : ByteArray) : String := CA.RefHash.toB58 b

private def sourcesArg (p : Cli.Parsed) : System.FilePath :=
  if p.hasFlag "sources" then p.flag! "sources" |>.as! String else CA.Sources.defaultPath

private def cacheArg (p : Cli.Parsed) : System.FilePath :=
  if p.hasFlag "cache" then p.flag! "cache" |>.as! String else CA.Sources.defaultCacheDir

private def readSourcesOrExit (p : Cli.Parsed) : IO CA.Sources.SourcesFile := do
  let path := sourcesArg p
  match ← CA.Sources.read path with
  | none => IO.eprintln s!"error: {path}: no such file"; IO.Process.exit 1
  | some (.error e) => IO.eprintln s!"error: {e}"; IO.Process.exit 1
  | some (.ok sf) => pure sf

/-- `ca lookup QUERY`: what every source says about a statement id (base58),
    a coarse hash (hex) or a name. Folder sources answer with their entries;
    node files also with declarations and witnesses. -/
def runLookupCmd (p : Cli.Parsed) : IO UInt32 := do
  let q := CA.Sources.Query.parse (p.positionalArg! "query" |>.as! String)
  let sf ← readSourcesOrExit p
  let cacheDir := cacheArg p
  let asJson := p.hasFlag "json"
  let mut out : Array Lean.Json := #[]
  let mut n := 0
  unless asJson do IO.println s!"{q}"
  for s in sf.sources do
    let path := CA.Sources.localPath s cacheDir
    match s.kind with
    | .folder =>
      match ← CA.Sources.readFolder path with
      | .error e =>
        IO.eprintln (if CA.Sources.isUrl s.location && !(← path.pathExists)
          then s!"  {s.name}: not fetched yet; run `ca fetch-sources`" else s!"  {s.name}: {e}")
      | .ok f =>
        for h in CA.Sources.lookupFolder s.name f q do
          n := n + 1
          if asJson then
            out := out.push (.mkObj [("source", s.name), ("project", f.project), ("toolchain", f.toolchain),
              ("name", h.entry.name.toString), ("kind", h.entry.kind), ("status", h.entry.status),
              ("stmt", h.entry.stmt), ("type_hash", h.entry.typeHash), ("pp_type", h.entry.ppType),
              ("proved_by", .arr (h.entry.provedBy.map (.str ·.toString))),
              ("status_deps", .arr (h.entry.statusDeps.map (.str ·.toString))),
              ("coarse", .bool h.coarse)])
          else IO.println s!"  {h.describe}"
    | .node =>
      unless ← path.pathExists do
        IO.eprintln (if CA.Sources.isUrl s.location then s!"  {s.name}: not fetched yet; run `ca fetch-sources`"
          else s!"  {s.name}: {path}: no such file")
        continue
      let db ← CA.NodeFile.openRead path
      let info ← CA.NodeFile.metaOf db
      let project := (info.find? (·.1 == "project")).map (·.2) |>.getD "?"
      let toolchain := (info.find? (·.1 == "lean_toolchain")).map (·.2) |>.getD "?"
      -- Entries (registry statements with a status), then declarations.
      let entries ← match q with
        | .stmt b => CA.NodeFile.entriesByStmt db (CA.Base58.decode b).get!
        | .typeHash h => CA.NodeFile.entriesByTypeHash db h
        | .name nm => CA.NodeFile.entriesByName db nm.toString
      let decls ← match q with
        | .stmt b => CA.NodeFile.declarationsByStmt db (CA.Base58.decode b).get!
        | .typeHash _ => pure #[]
        | .name nm => CA.NodeFile.declarationsByName db nm.toString
      for e in entries do
        n := n + 1
        let ws ← CA.NodeFile.witnessesOf db e.stmt
        if asJson then
          out := out.push (.mkObj [("source", s.name), ("project", project), ("toolchain", toolchain),
            ("name", e.name.toString), ("status", e.status), ("stmt", b58 e.stmt), ("type_hash", e.typeHash),
            ("witnesses", .arr (ws.map (.str <| b58 ·))), ("coarse", .bool (match q with | .typeHash _ => true | _ => false))])
        else
          IO.println s!"  {e.name} [{s.name}, {project}, {toolchain}]: entry, {e.status}; {ws.size} witness{if ws.size == 1 then "" else "es"} in this node{match q with | .typeHash _ => " (coarse match: type_hash only)" | _ => ""}\n    stmt {b58 e.stmt}"
      for d in decls do
        n := n + 1
        if asJson then
          out := out.push (.mkObj [("source", s.name), ("project", project), ("toolchain", toolchain),
            ("names", .arr (d.names.map (.str ·.toString))), ("kind", d.kind), ("decl", b58 d.decl),
            ("stmt", b58 d.stmt), ("ref", b58 d.ref)])
        else
          IO.println s!"  {", ".intercalate (d.names.toList.map toString)} [{s.name}, {project}, {toolchain}]: {d.kind}, decl {b58 d.decl}\n    stmt {b58 d.stmt}"
  if asJson then IO.println (Lean.Json.arr out).pretty
  else IO.println s!"{n} {if n == 1 then "answer" else "answers"} from {sf.sources.size} source{if sf.sources.size == 1 then "" else "s"}"
  return if n > 0 then 0 else 2

def lookupCmd : Cli.Cmd := `[Cli|
  lookup VIA runLookupCmd; ["0.3.0"]
  "Ask every source in sources.json about a statement id (base58), a coarse hash (hex) or a name. Exit 2 when nothing answers."

  FLAGS:
    sources : String; "The sources list (default: sources.json)"
    cache : String; "Local copies of URL sources (default: .lake/ca/sources)"
    json; "Machine-readable output"

  ARGS:
    query : String; "stmt (base58), type_hash (hex) or a declaration name"
]

private def curl (url : String) (dest : System.FilePath) : IO Bool := do
  let r ← IO.Process.output { cmd := "curl", args := #["-fsSL", "--retry", "2", "-o", dest.toString, url] }
  if r.exitCode != 0 then IO.eprintln s!"  curl {url}: {r.stderr.trimAscii}"
  return r.exitCode == 0

/-- `ca fetch-sources`: copy every URL source into the cache directory
    (folder: `declarations.json`, `statements.json`, `meta.json`; node: the
    file). Local sources need no fetch. -/
def runFetchSourcesCmd (p : Cli.Parsed) : IO UInt32 := do
  let sf ← readSourcesOrExit p
  let cacheDir := cacheArg p
  let refresh := p.hasFlag "refresh"
  let mut failed := 0
  for s in sf.sources do
    unless CA.Sources.isUrl s.location do
      IO.println s!"  {s.name}: local ({s.location}), nothing to fetch"
      continue
    let dest := CA.Sources.cachePath s cacheDir
    if !refresh && (← dest.pathExists) then
      IO.println s!"  {s.name}: cached at {dest} (use --refresh to fetch again)"
      continue
    match s.kind with
    | .node =>
      IO.FS.createDirAll cacheDir
      if ← curl s.location dest then IO.println s!"  {s.name}: fetched {dest}" else failed := failed + 1
    | .folder =>
      IO.FS.createDirAll dest
      let base := if s.location.endsWith "/" then s.location else s.location ++ "/"
      let mut ok := true
      for f in ["declarations.json", "meta.json", "statements.json"] do
        unless ← curl (base ++ f) (dest / f) do
          if f == "declarations.json" then ok := false
      if ok then IO.println s!"  {s.name}: fetched into {dest}"
      else
        failed := failed + 1
        try IO.FS.removeDirAll dest catch _ => pure ()
  return if failed == 0 then 0 else 1

def fetchSourcesCmd : Cli.Cmd := `[Cli|
  "fetch-sources" VIA runFetchSourcesCmd; ["0.3.0"]
  "Copy the URL sources of sources.json into the local cache."

  FLAGS:
    sources : String; "The sources list (default: sources.json)"
    cache : String; "Cache directory (default: .lake/ca/sources)"
    refresh; "Fetch again even if a copy exists"
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
  selftest VIA runSelftestCmd; ["0.3.0"]
  "Check that the OpenSSL SHA-256 agrees with the library's pure implementation."
]

-- Top-level CLI

def caCmd : Cli.Cmd := `[Cli|
  ca NOOP; ["0.3.0"]
  "Content-addressed declaration hashing for Lean 4 environments."

  SUBCOMMANDS:
    fetchCmd;
    addressCmd;
    registryCmd;
    packCmd;
    checkCmd;
    verifyCmd;
    keygenCmd;
    mergeCmd;
    digestCmd;
    diffCmd;
    migrateCmd;
    lookupCmd;
    fetchSourcesCmd;
    selftestCmd
]

/-- An uncaught `IO` error would reach the runtime's own error printer,
    which crashes (SIGSEGV) instead of printing it; report it here. -/
def main (args : List String) : IO UInt32 := do
  try caCmd.validate args
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1

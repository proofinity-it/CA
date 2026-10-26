import Lean
import CA.Base58
import CA.SHA256
import CA.RefHash

/-!
# CA.Sources — the sources list, and reading registry folders

`registry-protocol.md` §11: a reader keeps a list of the registries it
consults. `sources.json` is that list. Each source is a **folder** (a
project's `registry/`, the JSON files `#ca_registry` writes) or a
**node** (a node file, `payload.md` §6), given by a local path or a URL.

This module is pure Lean: it parses the list, reads folder sources
(JSON) and answers lookups over them, so `#ca_lookup` and `resolve%`
work inside a `lake build` with nothing to install. A URL source is
read from its local copy under `cacheDir`; fetching it there is the
`ca` CLI's job (`ca fetch-sources`), and so is reading node sources,
which need SQLite (`nodefile/`).

```json
{ "sources": [
    { "name": "mathlib-registry", "kind": "folder",
      "location": "https://example.org/mathlib/registry" },
    { "name": "local-proofs", "kind": "node", "location": "../proofs/node.sqlite" } ] }
```

`name` is a label for messages; `kind` is `folder` or `node`; `location`
is a path (relative to the project root) or an `http(s)` URL; `key`
(optional) is the signing key the source is expected to carry once
signed manifests exist (`registry-protocol.md` §11); it is parsed and
kept, not yet checked.
-/

open Lean

namespace CA.Sources

inductive Kind where
  | folder | node
  deriving BEq, Repr, Inhabited

def Kind.toString : Kind → String
  | .folder => "folder"
  | .node => "node"

instance : ToString Kind := ⟨Kind.toString⟩

structure Source where
  name : String
  kind : Kind
  location : String
  key : Option String := none
  deriving Repr, Inhabited

structure SourcesFile where
  sources : Array Source
  deriving Repr, Inhabited

/-- The default sources list of a project. -/
def defaultPath : System.FilePath := "sources.json"

/-- Where the CLI puts local copies of URL sources. -/
def defaultCacheDir : System.FilePath := ".lake" / "ca" / "sources"

def isUrl (s : String) : Bool :=
  s.startsWith "http://" || s.startsWith "https://"

def parse (text : String) : Except String SourcesFile := do
  let j ← Json.parse text
  let arr ← match j.getObjValD "sources" with
    | .arr a => pure a
    | .null => throw "sources.json: no \"sources\" array"
    | _ => throw "sources.json: \"sources\" is not an array"
  let mut out := #[]
  for i in [:arr.size] do
    let s : Json := arr[i]!
    let name := (s.getObjValAs? String "name").toOption.getD s!"source {i}"
    let location ← match (s.getObjValAs? String "location" : Except String String) with
      | .ok l => pure l
      | .error _ => throw s!"sources.json: {name}: no \"location\""
    let kind ← match (s.getObjValAs? String "kind" : Except String String) with
      | .ok "folder" => pure Kind.folder
      | .ok "node" => pure Kind.node
      | .ok k => throw s!"sources.json: {name}: unknown kind \"{k}\" (folder or node)"
      | .error _ =>
        -- Infer: a node file ends in .sqlite, anything else is a folder.
        pure (if location.endsWith ".sqlite" then Kind.node else Kind.folder)
    let key := (s.getObjValAs? String "key").toOption
    out := out.push { name, kind, location, key }
  return { sources := out }

/-- Read and parse a sources list; `none` if the file does not exist. -/
def read (path : System.FilePath := defaultPath) : IO (Option (Except String SourcesFile)) := do
  unless ← path.pathExists do return none
  return some (parse (← IO.FS.readFile path))

/-- The local copy of a URL source: a directory (folder) or a file (node)
    named by the digest of the URL. -/
def cachePath (s : Source) (cacheDir : System.FilePath := defaultCacheDir) : System.FilePath :=
  let tag := ((CA.SHA256.toHex256 (CA.SHA256.sha256Pure s.location.toUTF8)).take 16).toString
  match s.kind with
  | .folder => cacheDir / tag
  | .node => cacheDir / (tag ++ ".sqlite")

/-- Where a source is read from: its path, or its local copy for a URL. -/
def localPath (s : Source) (cacheDir : System.FilePath := defaultCacheDir) : System.FilePath :=
  if isUrl s.location then cachePath s cacheDir else s.location

/-! ## Folder sources -/

/-- One entry of a folder's `declarations.json` (`registry-design.md`). -/
structure FolderEntry where
  name : Name
  module : Name
  kind : String
  status : String
  /-- Exact tier, base58. -/
  stmt : String
  /-- What a dependent embeds, base58. -/
  ref : String
  /-- Coarse tier, hex. -/
  typeHash : String
  ppType : String
  description : String := ""
  proves : Array Name := #[]
  provedBy : Array Name := #[]
  statusDeps : Array Name := #[]
  unresolved : Array Name := #[]
  deriving Repr, Inhabited

structure Folder where
  project : String
  toolchain : String
  schemeVersion : Nat
  entries : Array FolderEntry
  deriving Repr, Inhabited

private def names (j : Json) (k : String) : Array Name :=
  match j.getObjValD k with
  | .arr a => a.filterMap fun x => x.getStr?.toOption.map String.toName
  | _ => #[]

private def str (j : Json) (k : String) : String :=
  (j.getObjValAs? String k).toOption.getD ""

def entryOfJson (j : Json) : Except String FolderEntry := do
  let name := str j "name"
  if name.isEmpty then throw "entry without a name"
  return { name := name.toName, module := (str j "module").toName, kind := str j "kind",
           status := str j "status", stmt := str j "stmt", ref := str j "ref",
           typeHash := str j "type_hash", ppType := str j "pp_type",
           description := str j "description", proves := names j "proves",
           provedBy := names j "proved_by", statusDeps := names j "status_deps",
           unresolved := names j "unresolved" }

/-- Read a registry folder: `declarations.json` and `meta.json`. -/
def readFolder (dir : System.FilePath) : IO (Except String Folder) := do
  let declsPath := dir / "declarations.json"
  unless ← declsPath.pathExists do return .error s!"{declsPath}: no such file"
  let decls ← IO.FS.readFile declsPath
  let metaTxt ← try IO.FS.readFile (dir / "meta.json") catch _ => pure "{}"
  return do
    let j ← Json.parse decls
    let arr ← match j with
      | .arr a => pure a
      | _ => throw s!"{declsPath}: not an array"
    let entries ← arr.mapM entryOfJson
    let m := (Json.parse metaTxt).toOption.getD (.mkObj [])
    let scheme := (m.getObjValAs? Nat "ca_scheme_version").toOption.getD 0
    return { project := str m "project", toolchain := str m "lean_toolchain",
             schemeVersion := scheme, entries }

/-! ## Lookups -/

/-- What a lookup asks for. -/
inductive Query where
  /-- Exact: a `stmt` id, base58. -/
  | stmt (b58 : String)
  /-- Coarse: a `type_hash`, hex. -/
  | typeHash (hex : String)
  /-- A declaration name, exact match on the dotted rendering. -/
  | name (n : Name)
  deriving Repr, Inhabited

/-- Parse a query string: base58 of 32 bytes is a `stmt`, 64 hex digits a
    `type_hash`, anything else a name. -/
def Query.parse (s : String) : Query :=
  if s.length == 64 && s.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then .typeHash s
  else match CA.Base58.decode s with
    | some b => if b.size == 32 then .stmt s else .name s.toName
    | none => .name s.toName

def Query.toString : Query → String
  | .stmt s => s!"stmt {s}"
  | .typeHash h => s!"type_hash {h}"
  | .name n => s!"name {n}"

instance : ToString Query := ⟨Query.toString⟩

/-- One answer: an entry of a source. -/
structure Hit where
  source : String
  project : String
  toolchain : String
  entry : FolderEntry
  /-- `true` when the match is on the coarse tier only. -/
  coarse : Bool := false
  deriving Repr, Inhabited

def matchQuery (q : Query) (e : FolderEntry) : Option Bool :=
  match q with
  | .stmt s => if e.stmt == s then some false else none
  | .typeHash h => if e.typeHash == h then some true else none
  | .name n => if e.name == n then some false else none

def lookupFolder (source : String) (f : Folder) (q : Query) : Array Hit :=
  f.entries.filterMap fun e =>
    (matchQuery q e).map fun coarse => { source, project := f.project, toolchain := f.toolchain, entry := e, coarse }

/-- Answer `q` from every folder source in order. Node sources are skipped
    here (the CLI reads them) and reported in the second component, as are
    unreadable folders. -/
def lookupFolders (sf : SourcesFile) (q : Query) (cacheDir : System.FilePath := defaultCacheDir)
    (root : System.FilePath := ".") : IO (Array Hit × Array String) := do
  let mut hits := #[]
  let mut notes := #[]
  for s in sf.sources do
    match s.kind with
    | .node => notes := notes.push s!"{s.name}: a node file; read it with `ca lookup`"
    | .folder =>
      let p := localPath s cacheDir
      let p := if p.isAbsolute then p else root / p
      match ← readFolder p with
      | .error e =>
        notes := notes.push (if isUrl s.location && !(← p.pathExists)
          then s!"{s.name}: not fetched yet; run `ca fetch-sources`" else s!"{s.name}: {e}")
      | .ok f => hits := hits ++ lookupFolder s.name f q
  return (hits, notes)

/-- One line per hit, for messages. -/
def Hit.describe (h : Hit) : String :=
  let e := h.entry
  let tier := if h.coarse then " (coarse match: type_hash only)" else ""
  let deps := if e.statusDeps.isEmpty then "" else s!" assuming {e.statusDeps}"
  let by_ := if e.provedBy.isEmpty then "" else s!" by {e.provedBy}"
  s!"{e.name} [{h.source}, {h.project}, {h.toolchain}]: {e.kind}, {e.status}{by_}{deps}{tier}\n    {e.ppType}\n    stmt {e.stmt}"

end CA.Sources

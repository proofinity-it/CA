import CA.Node
import SQLite

/-!
# The node file: a registry node as one SQLite file

`registry-protocol.md` §12 and `docs/payload.md` §6. `writeNode` writes
the rows of a `CA.Node.Node` to a new file; `readNode` reads them back.
A package of its own (`ca-nodefile`, in `nodefile/`) so that `require ca`
stays pure Lean: leansqlite compiles the SQLite amalgamation. The `ca`
CLI and declbuild both require it.
Ids and digests are 32-byte blobs. Names live once in `names`, as
`nm`-encoded blobs (`payload.md` §2) with a `display` column holding the
dotted rendering for people and SQL queries; every other table cites
them by position. Members cite their unit by row id.
-/

open Lean CA.Node CA.Payload

namespace CA.NodeFile

def schema : Array String := #[
  "CREATE TABLE meta (key TEXT PRIMARY KEY, value TEXT NOT NULL)",
  "CREATE TABLE refs (ix INTEGER PRIMARY KEY, ref BLOB NOT NULL)",
  "CREATE TABLE names (ix INTEGER PRIMARY KEY, name BLOB NOT NULL, display TEXT NOT NULL)",
  "CREATE TABLE units (id INTEGER PRIMARY KEY, key BLOB NOT NULL, variant BLOB NOT NULL, form INTEGER NOT NULL, bytes BLOB NOT NULL, UNIQUE (key, variant))",
  "CREATE TABLE members (decl BLOB NOT NULL, name INTEGER NOT NULL REFERENCES names, unit INTEGER NOT NULL REFERENCES units, member INTEGER NOT NULL, PRIMARY KEY (decl, name)) WITHOUT ROWID",
  "CREATE TABLE decorations (decl BLOB NOT NULL, name INTEGER NOT NULL REFERENCES names, bytes BLOB NOT NULL, UNIQUE (decl, name))",
  "CREATE TABLE declarations (decl BLOB PRIMARY KEY, kind TEXT NOT NULL, stmt BLOB NOT NULL, ref BLOB NOT NULL) WITHOUT ROWID",
  "CREATE TABLE witnesses (stmt BLOB NOT NULL, decl BLOB NOT NULL, PRIMARY KEY (stmt, decl)) WITHOUT ROWID",
  "CREATE TABLE entries (name INTEGER NOT NULL REFERENCES names, stmt BLOB NOT NULL, status TEXT NOT NULL, type_hash TEXT NOT NULL, PRIMARY KEY (name, stmt)) WITHOUT ROWID",
  "CREATE TABLE deps (decl BLOB NOT NULL, ref BLOB NOT NULL, PRIMARY KEY (decl, ref)) WITHOUT ROWID",
  "CREATE TABLE records (decl BLOB NOT NULL, digest BLOB PRIMARY KEY, json TEXT NOT NULL, signer TEXT NOT NULL, sig BLOB NOT NULL, valid INTEGER NOT NULL) WITHOUT ROWID",
  "CREATE TABLE namespaces (ns TEXT PRIMARY KEY, owner_key BLOB NOT NULL, delegates TEXT NOT NULL, sig BLOB NOT NULL)",
  "CREATE TABLE bindings (ns TEXT NOT NULL, name BLOB NOT NULL, seq INTEGER NOT NULL, target BLOB NOT NULL, sig BLOB NOT NULL, PRIMARY KEY (ns, name, seq)) WITHOUT ROWID",
  "CREATE INDEX members_by_unit ON members (unit)",
  "CREATE INDEX records_by_decl ON records (decl)",
  "CREATE INDEX deps_by_ref ON deps (ref)",
  "CREATE INDEX declarations_by_stmt ON declarations (stmt)",
  "CREATE INDEX names_by_display ON names (display)"]

def nameBytes (n : Name) : ByteArray := putName .empty n

def nameOfBytes (b : ByteArray) : IO Name :=
  match Rd.run' getName b with
  | .ok n => pure n
  | .error e => throw (IO.userError s!"bad name blob: {e}")

def formOf : Int64 → IO Form
  | 0 => pure .statement | 1 => pure .standalone | 2 => pure .block
  | k => throw (IO.userError s!"bad form {k}")

/-- Write `node` to a new SQLite file at `path` (an existing file is replaced). -/
def writeNode (path : System.FilePath) (node : CA.Node.Node) : IO Unit := do
  if ← path.pathExists then IO.FS.removeFile path
  -- Member, decoration and entry names join the file's name table.
  let mut table0 := node.table
  let mut ixs : Std.HashMap Name Nat := {}
  for n in node.members.map (·.name) ++ node.decorations.map (·.name) ++ node.entries.map (·.name) do
    let (t, i) := table0.nameIx n
    table0 := t
    ixs := ixs.insert n i
  let table := table0
  let nameIx := ixs
  let unitId : Std.HashMap (ByteArray × ByteArray) Nat :=
    (node.units.mapIdx (·, ·)).foldl (fun m (i, u) => m.insert (u.key, u.variant) i) {}
  let db ← SQLite.openWith path .readWriteCreate
  for s in schema do db.exec s
  db.transaction do
    let ins {α : Type} (sql : String) (rows : Array α) (bind : SQLite.Stmt → α → IO Unit) : IO Unit := do
      let st ← db.prepare sql
      for r in rows do
        bind st r
        st.exec
        st.reset
        st.clearBindings
    let ix (n : Name) : Int64 := (nameIx.getD n 0).toInt64
    ins "INSERT INTO meta VALUES (?1, ?2)" node.info fun st (k, v) => do
      st.bindText 1 k; st.bindText 2 v
    ins "INSERT INTO refs VALUES (?1, ?2)" (table.refs.mapIdx (·, ·)) fun st (i, r) => do
      st.bindInt64 1 i.toInt64; st.bindBlob 2 r
    ins "INSERT INTO names VALUES (?1, ?2, ?3)" (table.names.mapIdx (·, ·)) fun st (i, n) => do
      st.bindInt64 1 i.toInt64; st.bindBlob 2 (nameBytes n); st.bindText 3 n.toString
    ins "INSERT INTO units VALUES (?1, ?2, ?3, ?4, ?5)" (node.units.mapIdx (·, ·)) fun st (i, u) => do
      st.bindInt64 1 i.toInt64; st.bindBlob 2 u.key; st.bindBlob 3 u.variant
      st.bindInt64 4 u.form.byte.toNat.toInt64; st.bindBlob 5 u.bytes
    ins "INSERT OR IGNORE INTO members VALUES (?1, ?2, ?3, ?4)" node.members fun st m => do
      st.bindBlob 1 m.decl; st.bindInt64 2 (ix m.name)
      st.bindInt64 3 (unitId.getD (m.key, m.variant) 0).toInt64; st.bindInt64 4 m.member.toInt64
    ins "INSERT OR IGNORE INTO decorations VALUES (?1, ?2, ?3)" node.decorations fun st d => do
      st.bindBlob 1 d.decl; st.bindInt64 2 (ix d.name); st.bindBlob 3 d.bytes
    ins "INSERT INTO declarations VALUES (?1, ?2, ?3, ?4)" node.declarations fun st d => do
      st.bindBlob 1 d.decl; st.bindText 2 d.kind; st.bindBlob 3 d.stmt; st.bindBlob 4 d.ref
    ins "INSERT INTO witnesses VALUES (?1, ?2)" node.witnesses fun st (s, d) => do
      st.bindBlob 1 s; st.bindBlob 2 d
    ins "INSERT INTO entries VALUES (?1, ?2, ?3, ?4)" node.entries fun st e => do
      st.bindInt64 1 (ix e.name); st.bindBlob 2 e.stmt; st.bindText 3 e.status; st.bindText 4 e.typeHash
    ins "INSERT OR IGNORE INTO deps VALUES (?1, ?2)" node.deps fun st d => do
      st.bindBlob 1 d.decl; st.bindBlob 2 d.ref
    ins "INSERT OR REPLACE INTO records VALUES (?1, ?2, ?3, ?4, ?5, ?6)" node.records fun st r => do
      st.bindBlob 1 r.decl; st.bindBlob 2 r.digest; st.bindText 3 r.json; st.bindText 4 r.signer
      st.bindBlob 5 r.sig; st.bindInt64 6 (if r.valid then 1 else 0)
    ins "INSERT OR REPLACE INTO namespaces VALUES (?1, ?2, ?3, ?4)" node.namespaces fun st c => do
      st.bindText 1 c.ns; st.bindBlob 2 c.ownerKey; st.bindText 3 c.delegates; st.bindBlob 4 c.sig
    ins "INSERT OR REPLACE INTO bindings VALUES (?1, ?2, ?3, ?4, ?5)" node.bindings fun st b => do
      st.bindText 1 b.ns; st.bindBlob 2 (nameBytes b.name); st.bindInt64 3 b.seq.toInt64
      st.bindBlob 4 b.target; st.bindBlob 5 b.sig
  db.exec "VACUUM"

private def hasTable (db : SQLite) (name : String) : IO Bool := do
  let st ← db.prepare "SELECT 1 FROM sqlite_master WHERE type = 'table' AND name = ?1"
  st.bindText 1 name
  st.step

/-- The records of an open node file (none in a file written before the table existed). -/
def readRecords (db : SQLite) : IO (Array RecordRow) := do
  unless ← hasTable db "records" do return #[]
  let st ← db.prepare "SELECT decl, digest, json, signer, sig, valid FROM records ORDER BY decl, digest"
  let mut out := #[]
  while ← st.step do
    out := out.push { decl := ← st.columnBlob 0, digest := ← st.columnBlob 1, json := ← st.columnText 2,
                      signer := ← st.columnText 3, sig := ← st.columnBlob 4,
                      valid := (← st.columnInt64 5) != 0 : RecordRow }
  return out

/-- The namespace claims and bindings of an open node file. -/
def readNames (db : SQLite) : IO (Array NamespaceRow × Array BindingRow) := do
  unless ← hasTable db "bindings" do return (#[], #[])
  let st ← db.prepare "SELECT ns, owner_key, delegates, sig FROM namespaces ORDER BY ns"
  let mut ns := #[]
  while ← st.step do
    ns := ns.push { ns := ← st.columnText 0, ownerKey := ← st.columnBlob 1, delegates := ← st.columnText 2,
                    sig := ← st.columnBlob 3 : NamespaceRow }
  let st ← db.prepare "SELECT ns, name, seq, target, sig FROM bindings ORDER BY ns, name, seq"
  let mut bs := #[]
  while ← st.step do
    bs := bs.push { ns := ← st.columnText 0, name := ← nameOfBytes (← st.columnBlob 1),
                    seq := (← st.columnInt64 2).toNatClampNeg, target := ← st.columnBlob 3,
                    sig := ← st.columnBlob 4 : BindingRow }
  return (ns, bs)

/-- Add records to an existing node file (`ca verify --write`); a record
    with the same digest is replaced. -/
def appendRecords (path : System.FilePath) (records : Array RecordRow) : IO Unit := do
  unless ← path.pathExists do throw (IO.userError s!"{path}: no such file")
  let db ← SQLite.openWith path .readWrite
  db.exec "CREATE TABLE IF NOT EXISTS records (decl BLOB NOT NULL, digest BLOB PRIMARY KEY, json TEXT NOT NULL, signer TEXT NOT NULL, sig BLOB NOT NULL, valid INTEGER NOT NULL) WITHOUT ROWID"
  db.exec "CREATE INDEX IF NOT EXISTS records_by_decl ON records (decl)"
  db.transaction do
    let st ← db.prepare "INSERT OR REPLACE INTO records VALUES (?1, ?2, ?3, ?4, ?5, ?6)"
    for r in records do
      st.bindBlob 1 r.decl; st.bindBlob 2 r.digest; st.bindText 3 r.json; st.bindText 4 r.signer
      st.bindBlob 5 r.sig; st.bindInt64 6 (if r.valid then 1 else 0)
      st.exec; st.reset; st.clearBindings

/-- Read every row of a node file. -/
def readNode (path : System.FilePath) : IO CA.Node.Node := do
  unless ← path.pathExists do throw (IO.userError s!"{path}: no such file")
  let db ← SQLite.openWith path .readonly
  let rows {α : Type} (sql : String) (read : SQLite.Stmt → IO α) : IO (Array α) := do
    let st ← db.prepare sql
    let mut out := #[]
    while ← st.step do out := out.push (← read st)
    return out
  let info ← rows "SELECT key, value FROM meta ORDER BY key" fun st => do
    return (← st.columnText 0, ← st.columnText 1)
  let refs ← rows "SELECT ref FROM refs ORDER BY ix" (·.columnBlob 0)
  let names ← rows "SELECT name FROM names ORDER BY ix" fun st => do nameOfBytes (← st.columnBlob 0)
  let mut table : FileTable := {}
  for r in refs do table := (table.refIx r).1
  if table.refs.size != refs.size then throw (IO.userError s!"{path}: duplicate ids in refs")
  table := { table with names }
  let nameAt (i : Int64) : IO Name := match names[i.toNatClampNeg]? with
    | some n => pure n
    | none => throw (IO.userError s!"{path}: name {i} out of range")
  let units ← rows "SELECT key, variant, form, bytes FROM units ORDER BY id" fun st => do
    return { key := ← st.columnBlob 0, variant := ← st.columnBlob 1,
             form := ← formOf (← st.columnInt64 2), bytes := ← st.columnBlob 3 : UnitRow }
  let unitAt (i : Int64) : IO UnitRow := match units[i.toNatClampNeg]? with
    | some u => pure u
    | none => throw (IO.userError s!"{path}: unit {i} out of range")
  let members ← rows "SELECT decl, name, unit, member FROM members ORDER BY decl, name" fun st => do
    let u ← unitAt (← st.columnInt64 2)
    return { decl := ← st.columnBlob 0, name := ← nameAt (← st.columnInt64 1),
             key := u.key, variant := u.variant,
             member := (← st.columnInt64 3).toNatClampNeg : MemberRow }
  let decorations ← rows "SELECT decl, name, bytes FROM decorations ORDER BY decl, name" fun st => do
    return { decl := ← st.columnBlob 0, name := ← nameAt (← st.columnInt64 1),
             bytes := ← st.columnBlob 2 : DecorationRow }
  let declarations ← rows "SELECT decl, kind, stmt, ref FROM declarations ORDER BY decl" fun st => do
    return { decl := ← st.columnBlob 0, kind := ← st.columnText 1,
             stmt := ← st.columnBlob 2, ref := ← st.columnBlob 3 : DeclRow }
  let witnesses ← rows "SELECT stmt, decl FROM witnesses ORDER BY stmt, decl" fun st => do
    return (← st.columnBlob 0, ← st.columnBlob 1)
  let entries ← rows "SELECT name, stmt, status, type_hash FROM entries ORDER BY name, stmt" fun st => do
    return { name := ← nameAt (← st.columnInt64 0), stmt := ← st.columnBlob 1,
             status := ← st.columnText 2, typeHash := ← st.columnText 3 : EntryRow }
  let deps ← rows "SELECT decl, ref FROM deps ORDER BY decl, ref" fun st => do
    return { decl := ← st.columnBlob 0, ref := ← st.columnBlob 1 : DepRow }
  let records ← readRecords db
  let (namespaces, bindings) ← readNames db
  return { info, table, units, members, decorations, declarations, witnesses, entries, deps, records,
           namespaces, bindings }

/-! ## Queries

Answers over one node file without reading it whole (`registry-protocol.md`
§10): the entries, declarations and witnesses behind a statement id, a
coarse hash or a name. `ca lookup` asks these of every node source. -/

/-- A registry entry row, with its name resolved. -/
structure EntryHit where
  name : Name
  stmt : ByteArray
  status : String
  typeHash : String
  deriving Inhabited

/-- A declaration row with the names the file binds it to. -/
structure DeclHit where
  decl : ByteArray
  kind : String
  stmt : ByteArray
  ref : ByteArray
  names : Array Name
  deriving Inhabited

def openRead (path : System.FilePath) : IO SQLite := do
  unless ← path.pathExists do throw (IO.userError s!"{path}: no such file")
  SQLite.openWith path .readonly

private def rowsOf {α : Type} (db : SQLite) (sql : String) (bind : SQLite.Stmt → IO Unit)
    (read : SQLite.Stmt → IO α) : IO (Array α) := do
  let st ← db.prepare sql
  bind st
  let mut out := #[]
  while ← st.step do out := out.push (← read st)
  return out

def metaOf (db : SQLite) : IO (Array (String × String)) :=
  rowsOf db "SELECT key, value FROM meta ORDER BY key" (fun _ => pure ()) fun st => do
    return (← st.columnText 0, ← st.columnText 1)

private def readEntry (st : SQLite.Stmt) : IO EntryHit := do
  return { name := ← nameOfBytes (← st.columnBlob 0), stmt := ← st.columnBlob 1,
           status := ← st.columnText 2, typeHash := ← st.columnText 3 }

private def entrySelect := "SELECT n.name, e.stmt, e.status, e.type_hash FROM entries e JOIN names n ON e.name = n.ix"

def entriesByStmt (db : SQLite) (stmt : ByteArray) : IO (Array EntryHit) :=
  rowsOf db (entrySelect ++ " WHERE e.stmt = ?1 ORDER BY n.display") (·.bindBlob 1 stmt) readEntry

def entriesByTypeHash (db : SQLite) (typeHash : String) : IO (Array EntryHit) :=
  rowsOf db (entrySelect ++ " WHERE e.type_hash = ?1 ORDER BY n.display") (·.bindText 1 typeHash) readEntry

def entriesByName (db : SQLite) (display : String) : IO (Array EntryHit) :=
  rowsOf db (entrySelect ++ " WHERE n.display = ?1") (·.bindText 1 display) readEntry

/-- Every name the file binds to `decl` (twins are several). -/
def namesOfDecl (db : SQLite) (decl : ByteArray) : IO (Array Name) :=
  rowsOf db "SELECT n.name FROM members m JOIN names n ON m.name = n.ix WHERE m.decl = ?1 ORDER BY n.display"
    (·.bindBlob 1 decl) fun st => do nameOfBytes (← st.columnBlob 0)

private def withNames (db : SQLite) (rows : Array (ByteArray × String × ByteArray × ByteArray)) :
    IO (Array DeclHit) :=
  rows.mapM fun (decl, kind, stmt, ref) => do
    return { decl, kind, stmt, ref, names := ← namesOfDecl db decl }

private def readDeclRow (st : SQLite.Stmt) : IO (ByteArray × String × ByteArray × ByteArray) := do
  return (← st.columnBlob 0, ← st.columnText 1, ← st.columnBlob 2, ← st.columnBlob 3)

/-- The declarations whose statement is `stmt`: theorems proving it, or the
    definition it is the type of. -/
def declarationsByStmt (db : SQLite) (stmt : ByteArray) : IO (Array DeclHit) := do
  withNames db (← rowsOf db "SELECT decl, kind, stmt, ref FROM declarations WHERE stmt = ?1 ORDER BY decl"
    (·.bindBlob 1 stmt) readDeclRow)

def declaration (db : SQLite) (decl : ByteArray) : IO (Option DeclHit) := do
  let rows ← withNames db (← rowsOf db "SELECT decl, kind, stmt, ref FROM declarations WHERE decl = ?1"
    (·.bindBlob 1 decl) readDeclRow)
  return rows[0]?

/-- The declarations bound to a name (its dotted rendering). -/
def declarationsByName (db : SQLite) (display : String) : IO (Array DeclHit) := do
  withNames db (← rowsOf db
    "SELECT d.decl, d.kind, d.stmt, d.ref FROM members m JOIN names n ON m.name = n.ix JOIN declarations d ON d.decl = m.decl WHERE n.display = ?1 ORDER BY d.decl"
    (·.bindText 1 display) readDeclRow)

/-- Witness `decl`s of `stmt` (theorems with that statement). -/
def witnessesOf (db : SQLite) (stmt : ByteArray) : IO (Array ByteArray) :=
  rowsOf db "SELECT decl FROM witnesses WHERE stmt = ?1 ORDER BY decl" (·.bindBlob 1 stmt) (·.columnBlob 0)

end CA.NodeFile

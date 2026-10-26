# The walkthrough, step by step

`examples/walkthrough.sh` runs the `ca` CLI over the two example projects,
[`examples/publish`](../examples/publish) and
[`examples/consume`](../examples/consume), printing each command before
its output. CI runs it on every push, so what this page describes is
what the current code does. Run it yourself after building the CLI:

```bash
cd cli && lake build && cd ..
bash examples/walkthrough.sh
```

Two things to know before reading the output.

- **It leaves nothing behind.** Node files and the key go to a temporary
  directory that is deleted when the script ends. To keep a file, run the
  command by hand in `examples/publish` (its `.gitignore` covers
  `*.sqlite`, `*.key` and `sources.json`), or copy the script's lines.
- **`lake env` matters.** `ca pack` and `ca verify` load a Lean
  environment, so they run under `lake env` inside the project, which
  puts the project's `.olean`s and dependencies on the search path. `ca
  check`, `merge`, `diff`, `digest`, `migrate` and `lookup` read files only
  and need no environment.

The transcript below is abridged: `$WORK` is the temporary directory,
`ca` the CLI binary, Lake's progress lines are dropped.

## 1. `publish`: `lake build` writes `registry/`

```
$ lake build
info: Publish.lean:23:0: CA registry: 13 entries — 3 open points (1 proved), 10 published: 5 proved, 2 conditional, 2 definitions, 1 axioms
info: Publish.lean:23:0: Unchanged …/examples/publish/registry/declarations.json, …/statements.json, …/meta.json
```

`#ca_registry "registry/"` at the end of `Publish.lean` runs during
elaboration. The folder is committed, so the usual message is
*Unchanged*: files are rewritten only when their content changes, which
keeps `git status` quiet and lets the end-to-end test fail if a rebuild
would change them.

The script then lists the entries:

```
Both           open         DWUJ9VWtwKry…
Conj           proved       ByKFv4nqHrcs…
Open1          open         9BuiQtQHty54…
…
cond1          conditional  7B8gYezVDEnd…
conj_literal   proved       ByKFv4nqHrcs…
conj_proof     proved       6MxgYZUpSXzH…
```

Note `Conj` and `conj_literal`: an `@[open_point]` definition and a
theorem that states its proposition literally have the same `stmt`.
That is how a proof is recognised by id, not by name: `Conj` is `proved
by conj_literal, conj_proof`. `conj_proof : Conj` states the *constant*,
so its own `stmt` differs; it counts as a proof of `Conj` by reference
instead. `cond1 : Open1 → …` is `conditional`: its hypothesis is a still
open point.

The Python checker then reads `statements.json`: 13 units, every `stmt`
recomputed from the unit's bytes alone, no Lean involved.

## 2. `consume`: a build that reads another project's registry

```
$ cat sources.json
{ "sources": [ { "name": "publish", "kind": "folder", "location": "../publish/registry" } ] }
$ lake build
info: Publish.lean:23:0: CA registry: 13 entries …
info: Publish.lean:23:0: Unchanged …/examples/publish/registry/…
info: Consume.lean:12:0: stmt ByKFv4nqHrcsFWuBFd7ihUXKFNEdMvFdMvjW7n8XE3nn: 2 entries
  Conj [publish, Publish, leanprover/lean4:v4.35.0]: definition, proved by #[conj_literal, conj_proof]
    ∀ (n : Nat), n + 0 = n
  conj_literal [publish, Publish, leanprover/lean4:v4.35.0]: theorem, proved
info: Consume.lean:15:0: name cond1: 1 entry
  cond1 [publish, …]: theorem, conditional assuming #[Open1]
info: Consume.lean:16:0: type_hash d73f3967…: 2 entries
  Conj … (coarse match: type_hash only)
info: Consume.lean:31:0: CA registry: 14 entries — 3 open points (2 proved), 11 published: 8 proved, 0 conditional, …
```

Three things to note.

- The first two lines are `publish` being built *as a dependency* of
  `consume`. Its registry message appears in `consume`'s build, and the
  files land in `publish`'s own folder: `#ca_registry` resolves a
  relative directory against the module's package root, not the working
  directory. (Before v0.3.1 they landed in `consume/registry` and were
  overwritten a moment later.)
- `#ca_lookup` answers come from the folder named in `sources.json`,
  read during elaboration, as info messages. A coarse match is flagged
  as such: `type_hash` finds candidates, `stmt` confirms.
- Nothing is printed for `resolve%`. It elaborated: `add_zero_by_address`
  is a theorem whose proof is whatever `publish` binds to that address,
  here `conj_literal`. Change one character of the address in
  `Consume.lean` and the build fails with the sources' answer. The term
  is accepted only because the constant is in scope *and* recomputes to
  the same `stmt` in this environment; a source cannot bind an address
  to a declaration that means something else.

## 3. The cross-project cascade

```
Open1          proved       proves=[] proved_by=['solves_open1']
cond1          proved       proves=[] proved_by=[]
solves_open1   proved       proves=['Open1'] proved_by=[]
uses_wrap      proved       proves=[] proved_by=[]
```

`consume`'s registry has 14 entries: `publish`'s 13 (annotations are
inherited through the import) plus `solves_open1`. Statuses are
recomputed over that union: `Open1` is now proved, and `publish`'s
`cond1` and `uses_wrap`, conditional on it, are proved here. The
consumer computes this locally over what it holds; nothing was sent to
`publish`.

## 4. Node files: pack and check

```
$ lake env ca pack -m Publish --own -o $WORK/publish.sqlite
Loading environment for Publish...
Environment loaded: 210082 constants
Packing 52 root declarations (with proofs)...
Wrote $WORK/publish.sqlite: 52 declarations in 32 units, 13 registry statements; 105 refs, 122 names; 131072 bytes (0 s)
$ ca check $WORK/publish.sqlite
  …
$WORK/publish.sqlite: 44 units, 52 members, 34 decorations checked in 0 s
  ids recomputed from the units' bytes; 34 members rebuilt from their decorations to the same ids
  no faults
$ python3 -I tools/registry_ref.py $WORK/publish.sqlite
$WORK/publish.sqlite: 44 units, 52 members, 65 decorations; naming variants 0; inexact units 0
  no faults: every unit's ids recomputed from its bytes
```

- `--own` packs every declaration of the module, not only the annotated
  ones: 52 declarations (auxiliaries, `Color`, `twice`, the spec's `T`)
  in 32 units, because a block (an inductive with its constructors, a
  mutual family) is one unit. The 13 registry statements are units too
  (form 0), hence 44 units checked.
- The environment loaded is the whole import closure, 210,082
  constants, because `Publish` imports `CA` and so Batteries. Nothing of
  it is packed: dependencies are referenced by id.
- The two checkers count decorations differently and both are right:
  Lean reports the decorations it rebuilt declarations from (one per
  member position per unit, 34), Python every decoration row, statement
  decorations included (65). Both recompute every unit's ids from its
  bytes and the file's ref table; neither trusts a stored id.

## 5. A key, and a signed pack

```
$ ca keygen $WORK/example.key
secret key written to $WORK/example.key (keep it private); the line above is the public key …
F3nm2iV3wE3pv91YeWLKvC5Dkrb2iy49sWGLXRSbNooB
$ lake env ca pack -m Publish --own --sign $WORK/example.key --label publish -o $WORK/publish-signed.sqlite
  13 bindings in publish@F3nm2iV3wE3pv91YeWLKvC5Dkrb2iy49sWGLXRSbNooB
```

The key is Ed25519, generated and used in pure Lean; the public key is
printed in base58 and is the `key` part of the namespace id
`publish@key`. `--sign` writes a namespace claim and one binding per
registry entry, `name ↦ ref`, each signed and numbered. `ca check`
verifies the claim under the key in the id and every binding under the
owner's key, and that every target is in the file. Two publishers who
pick the label `publish` get two namespaces; nothing can collide.

## 6. The kernel's verdict

```
$ lake env ca verify $WORK/publish-signed.sqlite --write --sign $WORK/example.key
$WORK/publish-signed.sqlite: 50 declarations added and accepted by the kernel, 2 recursors produced by it, 0 already in the environment (0 s)
  13 records: 13 valid, 0 invalid (sorryAx)
  13 records written to $WORK/publish-signed.sqlite (signed by F3nm2iV3…)
  no faults
$ python3 -I tools/registry_ref.py $WORK/publish-signed.sqlite
  bindings: 13, signatures verified
  records: 13 (13 signed, signatures verified); derived over them: 11 statements proved, 0 conditional
```

This is the step the rest exists for. `ca check` showed the ids are
honest; `ca verify` shows the mathematics is: every declaration is
rebuilt from its unit and decorations, added to a fresh environment
(`Init` by default; `--import` for more) foundations first, and judged by
Lean's kernel. Nothing is trusted from the file but bytes. A forged
proof with honestly computed ids passes `ca check` and fails here
(`lake exe verify-test` does exactly that).

- "2 recursors produced by it": the kernel generates recursors itself;
  the file's `Color.rec` and `T.rec` are compared with the kernel's.
- A **record** per accepted theorem says what was *assumed* (ref ids of
  statements the environment did not have and the file did not prove)
  and which *axioms* the proof rests on. Here nothing is assumed and
  the only axioms are Lean's. A proof using `sorry` gets a record marked
  invalid, not conditional.
- `--write` stores the records in the file, `--sign` signs them. The
  Python checker verifies the signatures with its own Ed25519 and
  derives "proved" over the records: 13 records but 11 statements,
  because `Color` and `T` are twins (step 8), so `Color.red.sizeOf_spec`
  and `T.a.sizeOf_spec` are two witnesses of one statement, and likewise
  for `green` and `b`.

## 7. Merge

```
$ lake env ca pack -m Consume --own -o $WORK/consume.sqlite
Wrote $WORK/consume.sqlite: 2 declarations in 2 units, 14 registry statements; 18 refs, 20 names; 94208 bytes (0 s)
$ ca merge $WORK/union.sqlite $WORK/publish-signed.sqlite $WORK/consume.sqlite
Wrote $WORK/union.sqlite: 47 units, 36 declarations, 14 entries, 13 records, 13 bindings from 2 nodes; checked, no faults
```

`consume` has two declarations of its own and fourteen registry
statements (the inherited annotations again). The merge re-encodes
every unit of the second file against the first file's ref and name
tables, so the bytes change while the ids do not; records and bindings
are carried; entries are keyed by (name, `stmt`), so the same name with
two statements would be two entries. The result is checked before it is
written: a fault means no file.

## 8. Difference finding

```
$ ca diff $WORK/publish-signed.sqlite $WORK/consume.sqlite
43 bucket digests compared, 34 opened; 35 keys only in the first, 3 only in the second
  - 5PRqoKPV…  Conj
  - 39W2PKpM…  Color.red
  …
  - 6DDpCR3D…
  - E12cVn42…  Color.rec
  + 3tUXTS8x…
  + 8BVf4SUB…  solves_open1
  + 9wbk2xAa…  add_zero_by_address
```

Two nodes find what they lack by exchanging digests of id-prefix
buckets and opening only the buckets that differ. On files this small
most buckets hold one key, so most are opened; on a large file a few
digests settle most of the comparison.

Two kinds of line deserve a second look.

- Keys without a name (`6DDpCR3D…`, `3tUXTS8x…`) are not declarations:
  the first is the block id of `T` (the unit holding `T`, `T.a`, `T.b`),
  the second the statement unit of `solves_open1`.
- `Color.red` is listed under the key `39W2PKpM…`, which `spec.md` §12
  gives for `T.a`; `Color.rec` under `T.rec`'s key. `Color` and `T` are
  twins: structurally identical inductives with two constructors, hence
  one unit, one set of ids, two names each. The diff prints one name per
  key. Content addressing does not see names; the decorations do.

`ca diff` exits 2 when the nodes differ, which is why the script runs it
with `|| true`.

## 9. Asking every source

```
$ ca lookup --sources $WORK/sources.json ByKFv4nqHrcsFWuBFd7ihUXKFNEdMvFdMvjW7n8XE3nn
  Conj [publish-folder, Publish, …]: definition, proved by #[conj_literal, conj_proof]
  conj_literal [publish-folder, …]: theorem, proved
  Conj [union-node, Publish, Consume, …]: entry, proved; 2 witnesses in this node
  conj_literal [union-node, …]: entry, proved; 2 witnesses in this node
  conj_literal [union-node, …]: theorem, decl 6DaEHEsD…
  add_zero_by_address [union-node, …]: theorem, decl 9wbk2xAa…
6 answers from 2 sources
```

The same question to a folder and to a node file. The folder answers
with its entries; the node also with the declarations carrying the
statement, which is how one sees that `conj_literal` and
`add_zero_by_address` are two witnesses of one statement, with
different `decl` ids (different proofs) and one `stmt`. The merged
node's project reads `Publish, Consume`, the two it came from.

The script writes a `sources.json` with absolute paths because the node
file lives in the temporary directory; a project's own list uses paths
relative to its root, or URLs, which `ca fetch-sources` caches under
`.lake/ca/sources/`. `ca lookup` exits 2 when nothing answers.

## What to change, and what then needs changing

- Editing `Publish.lean` changes `registry/`: rebuild and commit the
  folder with the change, or `cli/tests/node-test.sh` fails. The same for
  `consume/registry/`, though nothing checks it yet.
- `Consume.lean` and step 9 of the script quote `Conj`'s address
  literally. If `Conj`'s statement changes, both need the new value from
  `publish/registry/declarations.json`.
- Adding an `@[open_point]` to `publish` and a theorem proving it in
  `consume` is the quickest way to watch the cascade in step 3 move.

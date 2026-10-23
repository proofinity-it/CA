# Examples

Two small Lean projects and a script, kept current by CI
(`cli/tests/node-test.sh` and `tools/fuzz_node.py` use `publish` as their
fixture; `walkthrough.sh` runs on every push). Nothing here depends on
anything outside this repository: `ca` is required by path, and
`lake build` is the only step.

| | what it shows |
|---|---|
| [`publish/`](publish) | a project that marks open points and theorems with `@[open_point]` / `@[publish]`; `lake build` writes `registry/`, committed here so the output can be read without building |
| [`consume/`](consume) | a project that requires `publish`, lists its registry in `sources.json`, asks it with `#ca_lookup`, cites a result by address with `resolve%`, and proves one of its open points, so its own registry shows the cross-project cascade |
| [`walkthrough.sh`](walkthrough.sh) | the CLI over the two: pack, check (Lean and Python), verify with signed records, sign names, merge, diff, lookup |

## Reading order

1. `publish/Publish.lean`, then `publish/registry/declarations.json`: each
   annotated declaration with its `stmt` (exact), `type_hash` (coarse),
   `ref`, its status and who proves what. `Conj` and `conj_literal` share
   a `stmt`: a theorem stating an open point's proposition literally is a
   proof of it, found by id, not by name.
2. `consume/sources.json` and `consume/Consume.lean`: `#ca_lookup` prints
   what the source says about a statement id, a name or a coarse hash,
   as an info message during `lake build`; `resolve% "<stmt>"` elaborates
   to `conj_literal`, because `publish` binds that address to it and the
   constant recomputes to the same `stmt` here. Change a byte of the
   address and the build fails with the sources' answer.
3. `consume/registry/declarations.json` after `lake build`: `solves_open1`
   proves `publish`'s `Open1`, and `publish`'s `cond1` and `uses_wrap`,
   conditional there, are `proved` here. That is the cross-project
   cascade, computed by the consumer over the union it holds.
4. `bash walkthrough.sh` (after `cd cli && lake build`): the same two
   projects as node files. Step 5 is the one that matters most: the
   kernel re-checks every declaration rebuilt from the file, and each
   theorem gets a signed record saying what was assumed and which axioms
   it rests on.

## Running

```bash
cd examples/publish && lake build            # writes registry/ (already committed)
cd ../consume && lake build                  # #ca_lookup prints, resolve% elaborates, registry/ written
cd ../../cli && lake build                   # the CLI, once
bash ../examples/walkthrough.sh              # pack, check, verify, sign, merge, diff, lookup
```

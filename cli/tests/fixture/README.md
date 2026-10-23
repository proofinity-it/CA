# Fixture: a small project with a registry

The example project the end-to-end test (`../node-test.sh`) and the fuzzer
(`tools/fuzz_node.py`) pack and check. It is also what a reader can look at
without building anything:

- `Fixture.lean`: open points, published theorems, a conditional theorem, a
  published definition and axiom, declarations with every status
  `#ca_registry` assigns, and the spec's `T` / `idT` for the test vectors.
- `registry/`: the folder `lake build` writes, committed so the output is
  visible: `declarations.json` (ids, statuses, who proves what),
  `statements.json` (each statement as a unit, checkable without Lean),
  `meta.json`. The test fails if a rebuild changes them.

To rebuild and pack:

```bash
lake build                                            # writes registry/
lake env ../../.lake/build/bin/ca pack -m Fixture --own -o node.sqlite
../../.lake/build/bin/ca check node.sqlite
lake env ../../.lake/build/bin/ca verify node.sqlite
```

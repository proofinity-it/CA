import Lake
open Lake DSL

/-! `examples/publish`: a project that publishes a registry. Open points,
published theorems, a conditional theorem, a definition and an axiom, so
every status `#ca_registry` assigns appears in `registry/`; plus the
spec's `T` / `idT` for the test vectors. It is also the fixture of
`cli/tests/node-test.sh` and `tools/fuzz_node.py`, which keeps it current.
Requires only `Init` and CA (by path). -/

package publish

require ca from "../.."

@[default_target]
lean_lib Publish

import Lake
open Lake DSL

/-! A small project for `cli/tests/node-test.sh`: the same annotated
declarations as `RegistryTest.lean`, compiled, so `ca pack` / `ca check`
run against real `.olean`s. Requires only `Init` (and CA). -/

package fixture

require ca from "../../.."

@[default_target]
lean_lib Fixture

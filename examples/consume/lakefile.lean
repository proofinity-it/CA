import Lake
open Lake DSL

/-! `examples/consume`: a project that reads another project's registry.
It depends on `publish` as a Lake package (so its constants are in scope)
and lists `publish`'s registry in `sources.json` (so statements can be
looked up and resolved by address). -/

package consume

require ca from "../.."
require publish from "../publish"

@[default_target]
lean_lib Consume

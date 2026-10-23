import Lake
open System Lake DSL

/-! The node file (`registry-protocol.md` §12, `docs/payload.md` §6): the
rows of a `CA.Node.Node` as one SQLite file. A separate package from the
library in `..` so that `require ca` stays pure Lean; leansqlite bundles
the SQLite amalgamation, so there is no system library to install.

Required by the `ca` CLI (`../cli`) and by any store that writes or reads
node files:

    require «ca-nodefile» from git "https://github.com/proofinity-it/CA" @ "vX.Y.Z" / "nodefile"
-/

package «ca-nodefile»

require ca from ".."

require leansqlite from git
  "https://github.com/leanprover/leansqlite" @ "v4.35.0"

@[default_target]
lean_lib CaNodeFile

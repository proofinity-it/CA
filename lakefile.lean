import Lake
open System Lake DSL

/-! The `ca` package is the content-addressing *library*: pure Lean, no
native dependencies, so `require ca` pulls in Batteries and nothing else.
The `ca` command-line tool (registry generation, node files, lookups,
kernel verification, signing, merge; plus bulk indexing into Redis; native
dependencies OpenSSL, hiredis and zlog) is the separate package in `cli/`. -/

package "ca"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.35.0"

/-- `precompileModules`: the interpreter (e.g. `#ca_registry` running during a
    downstream `lake build`) then executes CA's *compiled* code instead of
    interpreting it, which is what makes computing `RefHash` ids over an
    environment's statement cone affordable at elaboration time. -/
@[default_target]
lean_lib CA where
  precompileModules := true

/-- Property tests for `CA.RefHash` (elaborates a small source against `Init`). -/
lean_exe "refhash-test" where
  root := `CATest.RefHash
  supportInterpreter := true

/-- Status-classification tests for `CA.Registry` (elaborates a small source that imports `CA`). -/
lean_exe "registry-test" where
  root := `CATest.Registry
  supportInterpreter := true

/-- Round-trip tests for `CA.Payload` (units, decorations, checking) over `Init` and a small source. -/
lean_exe "payload-test" where
  root := `CATest.Payload
  supportInterpreter := true

/-- `CA.Node.packDecls` against `packEnvironment`: packing without an environment. -/
lean_exe "node-test" where
  root := `CATest.Node
  supportInterpreter := true

/-- `CA.Verify`: declarations rebuilt from a node and judged by the kernel; forged proofs rejected. -/
lean_exe "verify-test" where
  root := `CATest.Verify
  supportInterpreter := true

/-- `lake test`: the five test executables above, in order; stops at the first failure. -/
@[test_driver]
script test do
  for exe in ["refhash-test", "registry-test", "payload-test", "node-test", "verify-test"] do
    IO.println s!"── {exe}"
    let child ← IO.Process.spawn { cmd := "lake", args := #["exe", exe] }
    let code ← child.wait
    if code != 0 then
      IO.eprintln s!"{exe} failed (exit {code})"
      return code
  return 0

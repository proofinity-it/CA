# `publish`: a project that publishes a registry

`Publish.lean` marks what it offers the world:

- `@[open_point]` definitions: propositions nobody has proved here (`Open1`),
  one proved below (`Conj`), one carrying both attributes (`Both`);
- `@[publish]` theorems: one stating an open point's proposition literally
  (`conj_literal`), one proving the constant (`conj_proof`), theorems
  conditional on open points (`cond1`, `uses_wrap`), a definition and an
  axiom;
- unannotated declarations (`Color`, `twice`): in the module, hence in a
  `ca pack --own` node file, but not in the registry;
- the spec's `T` and `idT`, whose ids are `spec.md` §12's test vectors.

`#ca_registry "registry/"` at the end makes `lake build` write the folder,
committed here so the output is visible without building:

- `registry/declarations.json`: one entry per annotated declaration, with
  `stmt` (exact id), `type_hash` (coarse), `ref`, status, and who proves
  what (`proves`, `proved_by`, `status_deps`);
- `registry/statements.json`: each statement as a unit, from which anyone
  recomputes its `stmt` without Lean (`python3 -I ../../tools/registry_ref.py registry/statements.json`);
- `registry/meta.json`: counts, toolchain, scheme version.

Publishing is `git push`. The project `consume/` next door reads this
folder; `../walkthrough.sh` packs, checks, verifies, signs and merges it.

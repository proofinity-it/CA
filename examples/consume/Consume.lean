import CA
import Publish

/-! Consuming a registry (`docs/usage.md`, step 6).

`sources.json` names `../publish/registry`. Everything below works during
`lake build`, with no server and nothing installed beyond CA. -/

-- What does the registry say about this statement id? (It is `Conj`'s,
-- and `conj_literal`'s: a theorem stating an open point's proposition
-- shares its `stmt`. The value is in ../publish/registry/declarations.json.)
#ca_lookup "ByKFv4nqHrcsFWuBFd7ihUXKFNEdMvFdMvjW7n8XE3nn"

-- By name, and by the coarse hash (candidates across toolchains).
#ca_lookup "cond1"
#ca_lookup "d73f3967fc94d334681986a8fd4e9e327ed9eab8a5890cc007a0e804f0243ad8"

-- Cite a result by its address, not its name: `resolve%` is the proof a
-- source binds to the statement, accepted only because the constant is in
-- scope and recomputes to that very `stmt` here.
theorem add_zero_by_address : ∀ n : Nat, n + 0 = n :=
  resolve% "ByKFv4nqHrcsFWuBFd7ihUXKFNEdMvFdMvjW7n8XE3nn"

-- Discharging another project's open point. `Open1` is `publish`'s; this
-- registry classifies `solves_open1` as proving it, and `publish`'s
-- conditional theorems (`cond1`, `uses_wrap`) become proved in the union
-- of the two registries: the cross-project cascade, computed here.
@[publish "proves publish's Open1"]
theorem solves_open1 : Open1 := fun n => Nat.mul_one n

#ca_registry "registry/"

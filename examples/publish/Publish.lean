import CA
@[open_point "nobody proves this here"] def Open1 : Prop := ∀ n : Nat, n * 1 = n
@[open_point "proved below"] def Conj : Prop := ∀ n : Nat, n + 0 = n
@[publish] theorem conj_proof : Conj := fun n => Nat.add_zero n
@[publish] theorem conj_literal : ∀ n : Nat, n + 0 = n := fun n => Nat.add_zero n
@[publish] theorem uses_conj (h : Conj) : 1 + 0 = 1 := h 1
@[publish] theorem cond1 (h : Open1) : 2 * 1 = 2 := h 2
@[publish] def Wrap : Prop := Open1 ∧ True
@[publish] theorem uses_wrap (h : Wrap) : 2 * 1 = 2 := h.1 2
@[publish] theorem refut_shape : ¬ (Open1 ∧ False) := fun h => h.2
@[publish] theorem about : Open1 ∨ True := Or.inr trivial
@[open_point, publish "both"] def Both : Prop := ∀ n : Nat, n = n
@[publish] def notAProp : Nat := 3
@[publish] axiom ax : (1 : Nat) = 1
-- Not annotated, but in the module: packed by `ca pack --own`, absent from registry/.
inductive Color where | red | green
def Color.swap : Color → Color | .red => .green | .green => .red
theorem twice (n : Nat) : n + n = 2 * n := by omega
-- spec.md §12 Set A, for payload.md §9's test vectors.
inductive T where | a | b
def idT (x : T) : T := x

#ca_registry "registry/"

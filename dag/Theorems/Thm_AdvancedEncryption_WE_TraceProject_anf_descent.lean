import Mathlib

theorem AdvancedEncryption.WE.TraceProject.anf_descent {V : Type} [DecidableEq V] (S : Finset V) (terms : Finset (Finset V))
    (proper : ∀ T ∈ terms, T ⊂ S) (coeff : Finset V → ZMod 2) :
    let eval := fun U : Finset V ↦ ∑ T ∈ terms, if T ⊆ U then coeff T else 0
    eval S ≠ 0 → ∃ U, U ⊂ S ∧ eval U ≠ 0 := by
  sorry

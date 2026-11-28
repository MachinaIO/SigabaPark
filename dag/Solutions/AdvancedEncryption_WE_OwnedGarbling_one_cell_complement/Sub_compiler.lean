import Definitions.Def_OwnedGarbling

open OwnedGarbling
open scoped BigOperators

theorem solution {K : Type} [Fintype K] (test : Bool × K → ℝ) :
    (∑ v : Bool × K × K, test (!v.1, v.2.2)) =
      ∑ v : Bool × K × K, test (v.1, v.2.1) := by
  let e : (Bool × K × K) ≃ (Bool × K × K) := {
    toFun := fun v ↦ (!v.1, v.2.2, v.2.1)
    invFun := fun v ↦ (!v.1, v.2.2, v.2.1)
    left_inv := by intro v; rcases v with ⟨c,l,r⟩; cases c <;> rfl
    right_inv := by intro v; rcases v with ⟨c,l,r⟩; cases c <;> rfl }
  exact e.sum_comp (fun v ↦ test (v.1, v.2.1))

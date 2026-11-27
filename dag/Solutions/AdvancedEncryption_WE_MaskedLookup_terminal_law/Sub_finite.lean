import Mathlib
open scoped BigOperators

theorem solution {I : Type} [Fintype I] [DecidableEq I] (active truth cell : I → Bool)
    (test : (I → Bool) → ℝ) :
    (∑ v : I → Bool, test (fun i ↦ if active i then cell i else truth i ^^ v i)) =
      ∑ v : I → Bool, test (fun i ↦ if active i then cell i else v i) := by
  let e : (I → Bool) ≃ (I → Bool) := {
    toFun := fun v i ↦ truth i ^^ v i
    invFun := fun v i ↦ truth i ^^ v i
    left_inv := by intro v; funext i; cases truth i <;> simp
    right_inv := by intro v; funext i; cases truth i <;> simp }
  exact e.sum_comp (fun v ↦ test (fun i ↦ if active i then cell i else v i))

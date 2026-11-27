import Mathlib
open scoped BigOperators

theorem solution {I : Type} [Fintype I] [DecidableEq I] (theta : I → Bool) (kernel : (I → Bool) → ℝ) :
    (∑ pi : I → Bool, kernel (fun i ↦ theta i ^^ pi i)) = ∑ alpha : I → Bool, kernel alpha := by
  let e : (I → Bool) ≃ (I → Bool) := {
    toFun := fun v i ↦ theta i ^^ v i
    invFun := fun v i ↦ theta i ^^ v i
    left_inv := by intro v; funext i; cases theta i <;> simp
    right_inv := by intro v; funext i; cases theta i <;> simp }
  exact e.sum_comp kernel

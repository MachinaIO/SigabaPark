import Mathlib

open scoped BigOperators

theorem solution {I : Type} [Fintype I] [DecidableEq I]
    (side activeToken otherTruth : I → Bool) (test : (I → Bool × Bool) → ℝ) :
    (∑ h : I → Bool, test (fun i =>
      let other := otherTruth i ^^ h i
      (activeToken i ^^ other, if side i then other else activeToken i))) =
    ∑ p : I → Bool, test (fun i => (p i, activeToken i ^^ (side i && p i))) := by
  let e : (I → Bool) ≃ (I → Bool) := {
    toFun := fun h i => activeToken i ^^ (otherTruth i ^^ h i)
    invFun := fun p i => otherTruth i ^^ (activeToken i ^^ p i)
    left_inv := by
      intro h
      funext i
      dsimp only
      cases activeToken i <;> cases otherTruth i <;> cases h i <;> rfl
    right_inv := by
      intro p
      funext i
      dsimp only
      cases activeToken i <;> cases otherTruth i <;> cases p i <;> rfl }
  let sim := fun p : I → Bool => test (fun i => (p i, activeToken i ^^ (side i && p i)))
  calc
    _ = ∑ h : I → Bool, sim (e h) := by
      apply Finset.sum_congr rfl
      intro h _
      apply congrArg test
      funext i
      dsimp [e]
      cases side i <;> cases activeToken i <;> cases otherTruth i <;> cases h i <;> rfl
    _ = _ := e.sum_comp sim

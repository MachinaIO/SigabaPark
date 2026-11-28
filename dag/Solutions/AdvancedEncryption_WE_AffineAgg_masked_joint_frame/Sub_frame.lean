import Mathlib

theorem solution {I O Z : Type} [AddCommGroup Z] (u₀ u₁ v₀ v₁ : I → Z)
    (same : ∀ i, u₀ i + v₀ i = u₁ i + v₁ i)
    (test : (I → Z) → (I → Z) → O) (out : O) :
    Nonempty ({p : I → Z // test (fun i => p i + u₀ i) (fun i => v₀ i - p i) = out} ≃
      {p : I → Z // test (fun i => p i + u₁ i) (fun i => v₁ i - p i) = out}) := by
  let e : (I → Z) ≃ (I → Z) :=
    { toFun := fun p i => p i + u₀ i - u₁ i
      invFun := fun q i => q i + u₁ i - u₀ i
      left_inv := fun p => funext fun i => by change p i + u₀ i - u₁ i + u₁ i - u₀ i = p i; abel
      right_inv := fun p => funext fun i => by change p i + u₁ i - u₀ i + u₀ i - u₁ i = p i; abel }
  refine ⟨e.subtypeEquiv ?_⟩
  intro p
  have h₁ : (fun i => e p i + u₁ i) = (fun i => p i + u₀ i) := by
    funext i
    change p i + u₀ i - u₁ i + u₁ i = _
    abel
  have h₂ : (fun i => v₁ i - e p i) = (fun i => v₀ i - p i) := by
    funext i
    change v₁ i - (p i + u₀ i - u₁ i) = _
    have h := same i
    calc
      _ = (u₁ i + v₁ i) - u₀ i - p i := by abel
      _ = _ := by rw [← h]; abel
  rw [h₁,h₂]

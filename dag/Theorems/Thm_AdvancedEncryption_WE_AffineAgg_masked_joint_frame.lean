import Mathlib

theorem AdvancedEncryption.WE.AffineAgg.masked_joint_frame {I O Z : Type} [AddCommGroup Z] (u₀ u₁ v₀ v₁ : I → Z)
    (same : ∀ i, u₀ i + v₀ i = u₁ i + v₁ i)
    (test : (I → Z) → (I → Z) → O) (out : O) :
    Nonempty ({p : I → Z // test (fun i => p i + u₀ i) (fun i => v₀ i - p i) = out} ≃
      {p : I → Z // test (fun i => p i + u₁ i) (fun i => v₁ i - p i) = out}) := by
  sorry

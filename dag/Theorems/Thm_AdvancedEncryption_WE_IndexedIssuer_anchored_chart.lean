import Mathlib
/-- Address functions of the form a(i,j) plus b(j,k) have unique anchored coordinates. -/
theorem AdvancedEncryption.WE.IndexedIssuer.anchored_chart {I J K W : Type*} [AddCommGroup W] (i₀ : I) (k₀ : K)
    (a : I → J → W) (b : J → K → W) :
    ∃! p : (I → J → W) × (J → K → W),
      (∀ j, p.2 j k₀ = 0) ∧ (∀ i j k, p.1 i j + p.2 j k = a i j + b j k) := by sorry

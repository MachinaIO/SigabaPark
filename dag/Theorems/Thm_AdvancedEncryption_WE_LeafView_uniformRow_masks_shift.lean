import SigabaNeoStd.Lattices.LeftoverHash

open SigabaNeo.Lattices Cslib.Probability
open scoped ENNReal

theorem AdvancedEncryption.WE.LeafView.uniformRow_masks_shift {K V : Type} [CommRing K] [Fintype K] [DecidableEq K]
    {n m t : ℕ} [NeZero m]
    (post : Matrix (Option (Fin n)) (Fin m) K →
      (Fin t → Fin n → K) → (Fin t → K) → PMF V) (d₀ d₁ : Fin t → K) :
    let run := fun (d : Fin t → K) ↦
      (PMF.uniformOfFintype (Matrix (Option (Fin n)) (Fin m) K)).bind fun A ↦
        (Cslib.Probability.PMF.pi fun _ : Fin t ↦
          (PMF.uniformOfFintype (Fin m → Bool)).map (binaryHash A)).bind fun H ↦
            post A (fun i j ↦ H i (some j)) (fun i ↦ d i + H i none)
    let ε := ENNReal.ofReal ((t : ℝ) * (Real.sqrt
      ((Fintype.card K : ℝ) ^ (n + 1) * (2 ^ m : ℝ)⁻¹) / 2))
    CloseTo (run d₀) (run d₁) (ε + ε) := by
  sorry

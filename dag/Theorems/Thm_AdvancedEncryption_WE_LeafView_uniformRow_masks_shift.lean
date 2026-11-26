import SigabaNeoStd.Lattices.LeftoverHash

open SigabaNeo.Lattices Cslib.Probability
open scoped ENNReal

theorem AdvancedEncryption.WE.LeafView.uniformRow_masks_shift {K U : Type} [CommRing K] [Fintype K] [DecidableEq K]
    {n m t : ℕ} [NeZero m]
    (key : Matrix (Option (Fin n)) (Fin m) K → (Fin t → Fin m → Bool) → PMF U)
    (hkey : ∀ A x x', (∀ i j, binaryHash A (x i) (some j) = binaryHash A (x' i) (some j)) →
      key A x = key A x') (d₀ d₁ : Fin t → K) :
    let run := fun (d : Fin t → K) ↦
      (PMF.uniformOfFintype (Matrix (Option (Fin n)) (Fin m) K)).bind fun A ↦
        (Cslib.Probability.PMF.pi fun _ : Fin t ↦ PMF.uniformOfFintype (Fin m → Bool)).bind fun x ↦
          (key A x).map fun u ↦
            (A, (fun i j ↦ binaryHash A (x i) (some j)), u, (fun i ↦ d i + binaryHash A (x i) none))
    let ε := ENNReal.ofReal ((t : ℝ) * (Real.sqrt
      ((Fintype.card K : ℝ) ^ (n + 1) * (2 ^ m : ℝ)⁻¹) / 2))
    CloseTo (run d₀) (run d₁) (ε + ε) := by
  sorry

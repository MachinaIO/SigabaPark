import Definitions.Def_TerminalRectangle


open TerminalRectangle

theorem AdvancedEncryption.WE.Rectangle.hardAt (r₀ r₁ g₀ g₁ : PMF (List Bool)) (D k h : ℕ)
    (hard : (SigabaNeo.Problem.decision g₀ g₁).HardAt h)
    (hybrids : ∀ A : SigabaNeo.Machine, ∃ p : ℕ → ℝ,
      p 0 = A.acceptProb r₀ ∧ p (2 * D) = A.acceptProb r₁ ∧
      ∀ t < 2 * D, ∃ B : SigabaNeo.Machine,
        |p t - p (t+1)| ≤ |B.acceptProb g₀ - B.acceptProb g₁| ∧
        (2 : ℝ)^k * (2 * D : ℝ)^2 * B.cost ≤ (2 : ℝ)^h * A.cost) :
    (SigabaNeo.Problem.decision r₀ r₁).HardAt k := by sorry

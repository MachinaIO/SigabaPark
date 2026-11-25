import SigabaNeo.Trusted.Assumption

theorem AdvancedEncryption.WE.Hybrid.hardAt_chain (D : ℕ → PMF (List Bool)) (T k : ℕ)
    (h : ∀ i < T, (SigabaNeo.Problem.decision (D i) (D (i + 1))).HardAt k) (A : SigabaNeo.Machine) :
    (2 : ℝ) ^ k * (SigabaNeo.Problem.decision (D 0) (D T)).gain A ≤ (T : ℝ) ^ 2 * A.cost := by sorry

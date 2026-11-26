import SigabaNeo.Trusted.Assumption

open SigabaNeo

theorem AdvancedEncryption.WE.Premise.hardAt_of_reduction (P Q : Problem) (H k : ℕ) (α β p : ℝ)
    (hβ : 0 ≤ β) (hp : 0 < p) (hQ : Q.HardAt H)
    (hred : ∀ A : Machine, P.gain A = 0 ∨
      ∃ B : Machine, P.gain A ≤ Q.gain B ∧ (B.cost : ℝ) ≤ α * A.cost + β ∧ p ≤ A.cost)
    (hk : (2 : ℝ) ^ k * (α + β / p) ≤ 2 ^ H) :
    P.HardAt k := by sorry

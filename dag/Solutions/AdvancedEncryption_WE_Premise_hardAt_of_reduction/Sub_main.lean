import SigabaNeo.Trusted.Assumption

open SigabaNeo

theorem solution (P Q : Problem) (H k : ℕ) (α β p : ℝ) (hβ : 0 ≤ β) (hp : 0 < p)
    (hQ : Q.HardAt H)
    (hred : ∀ A : Machine, P.gain A = 0 ∨
      ∃ B : Machine, P.gain A ≤ Q.gain B ∧ (B.cost : ℝ) ≤ α * A.cost + β ∧ p ≤ A.cost)
    (hk : (2 : ℝ) ^ k * (α + β / p) ≤ 2 ^ H) :
    P.HardAt k := by
  intro A
  rcases hred A with h0 | ⟨B, hg, hc, hpc⟩
  · rw [h0, mul_zero]; exact_mod_cast Nat.zero_le _
  · have hA : (0 : ℝ) ≤ A.cost := by exact_mod_cast Nat.zero_le _
    have hβc : β ≤ β / p * A.cost := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hp]
      exact mul_le_mul_of_nonneg_left hpc hβ
    have hB : (2 : ℝ) ^ H * Q.gain B ≤ B.cost := hQ B
    have h2H : (0 : ℝ) < 2 ^ H := by positivity
    have hgB : Q.gain B ≤ (α + β / p) * A.cost / 2 ^ H := by
      rw [le_div_iff₀ h2H]
      calc Q.gain B * 2 ^ H = 2 ^ H * Q.gain B := by ring
        _ ≤ B.cost := hB
        _ ≤ α * A.cost + β := hc
        _ ≤ α * A.cost + β / p * A.cost := by linarith
        _ = (α + β / p) * A.cost := by ring
    have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
    calc (2 : ℝ) ^ k * P.gain A ≤ 2 ^ k * Q.gain B := mul_le_mul_of_nonneg_left hg h2k
      _ ≤ 2 ^ k * ((α + β / p) * A.cost / 2 ^ H) := mul_le_mul_of_nonneg_left hgB h2k
      _ = (2 ^ k * (α + β / p)) * A.cost / 2 ^ H := by ring
      _ ≤ 2 ^ H * A.cost / 2 ^ H := by
          apply div_le_div_of_nonneg_right _ h2H.le
          exact mul_le_mul_of_nonneg_right hk hA
      _ = A.cost := by field_simp

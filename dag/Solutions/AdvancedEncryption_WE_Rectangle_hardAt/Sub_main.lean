import Definitions.Def_TerminalRectangle


open TerminalRectangle

private theorem numericTransfer (adv eps cost sim : ℝ) (D k h : ℕ)
    (hadv : |adv| ≤ (2 * D : ℝ) * eps)
    (hstep : (2 : ℝ)^h * eps^2 ≤ sim)
    (hbudget : (2 : ℝ)^k * (2 * D : ℝ)^2 * sim ≤ (2 : ℝ)^h * cost) :
    (2 : ℝ)^k * adv^2 ≤ cost := by
  have he : 0 ≤ (2 * D : ℝ) * eps := (abs_nonneg _).trans hadv
  have hs := mul_self_le_mul_self (abs_nonneg _) hadv
  rw [← sq, sq_abs] at hs
  have hsq : adv^2 ≤ (2 * D : ℝ)^2 * eps^2 := by nlinarith only [hs]
  have hscaled := mul_le_mul_of_nonneg_left hstep (show 0 ≤ (2:ℝ)^k*(2*D:ℝ)^2 by positivity)
  have combined : (2:ℝ)^h * ((2:ℝ)^k*adv^2) ≤ (2:ℝ)^h * cost := calc
    _ ≤ (2:ℝ)^h * ((2:ℝ)^k*((2*D:ℝ)^2*eps^2)) := by gcongr
    _ = ((2:ℝ)^k*(2*D:ℝ)^2)*((2:ℝ)^h*eps^2) := by ring
    _ ≤ _ := hscaled.trans hbudget
  exact le_of_mul_le_mul_left combined (by positivity)

theorem solution (r₀ r₁ g₀ g₁ : PMF (List Bool)) (D k h : ℕ)
    (hard : (SigabaNeo.Problem.decision g₀ g₁).HardAt h)
    (hybrids : ∀ A : SigabaNeo.Machine, ∃ p : ℕ → ℝ,
      p 0 = A.acceptProb r₀ ∧ p (2 * D) = A.acceptProb r₁ ∧
      ∀ t < 2 * D, ∃ B : SigabaNeo.Machine,
        |p t - p (t+1)| ≤ |B.acceptProb g₀ - B.acceptProb g₁| ∧
        (2 : ℝ)^k * (2 * D : ℝ)^2 * B.cost ≤ (2 : ℝ)^h * A.cost) :
    (SigabaNeo.Problem.decision r₀ r₁).HardAt k := by
  intro A
  obtain ⟨p, h₀, h₁, steps⟩ := hybrids A
  change (2 : ℝ)^k * (A.acceptProb r₀ - A.acceptProb r₁)^2 ≤ A.cost
  rw [← h₀, ← h₁]
  by_cases hd : 2 * D = 0
  · simp [hd]
  have hn : (Finset.range (2*D)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hd)⟩
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image _ (fun i => |p i - p (i+1)|) hn
  obtain ⟨B, hgap, hcost⟩ := steps t (Finset.mem_range.mp ht)
  have bound : |p 0 - p (2*D)| ≤ (2*D : ℝ) * |B.acceptProb g₀ - B.acceptProb g₁| := by
    calc
      _ = |∑ i ∈ Finset.range (2*D), (p i - p (i+1))| := by rw [Finset.sum_range_sub']
      _ ≤ ∑ i ∈ Finset.range (2*D), |p i - p (i+1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (2*D), |B.acceptProb g₀ - B.acceptProb g₁| :=
        Finset.sum_le_sum fun i hi => (hmax i hi).trans hgap
      _ = _ := by simp
  have hs := hard B
  change (2 : ℝ)^h * (B.acceptProb g₀ - B.acceptProb g₁)^2 ≤ B.cost at hs
  apply numericTransfer _ _ _ _ D k h bound _ hcost
  simpa only [sq_abs] using hs

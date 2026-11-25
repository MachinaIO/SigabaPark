import SigabaNeo.Trusted.Assumption

open SigabaNeo

theorem solution (D : ℕ → PMF (List Bool)) (T : ℕ) (C : Finset ℕ) (A : Machine) (ε δ : ℝ)
    (hdec : 1 - δ ≤ A.acceptProb (D 0) - A.acceptProb (D T))
    (hcomp : ∀ i ∈ C, |A.acceptProb (D i) - A.acceptProb (D (i + 1))| ≤ ε) :
    1 - δ - (C.card : ℝ) * ε ≤
      ∑ i ∈ (Finset.range T).filter (fun i => i ∉ C),
        |A.acceptProb (D i) - A.acceptProb (D (i + 1))| := by
  set d : ℕ → ℝ := fun i => A.acceptProb (D i) - A.acceptProb (D (i + 1)) with hd
  have htel : A.acceptProb (D 0) - A.acceptProb (D T) = ∑ i ∈ Finset.range T, d i := by
    rw [Finset.sum_range_sub' (fun i => A.acceptProb (D i))]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range T) (fun i => i ∈ C) d
  have hin : ∑ i ∈ (Finset.range T).filter (fun i => i ∈ C), d i ≤ (C.card : ℝ) * ε := by
    have h1 : ∑ i ∈ (Finset.range T).filter (fun i => i ∈ C), d i ≤
        ∑ i ∈ (Finset.range T).filter (fun i => i ∈ C), ε :=
      Finset.sum_le_sum fun i hi =>
        (le_abs_self _).trans (hcomp i (Finset.mem_filter.mp hi).2)
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    rcases C.eq_empty_or_nonempty with hC | ⟨c, hc⟩
    · subst hC; simp
    · have hε : 0 ≤ ε := (abs_nonneg _).trans (hcomp c hc)
      have hcard : (((Finset.range T).filter (fun i => i ∈ C)).card : ℝ) ≤ C.card := by
        exact_mod_cast Finset.card_le_card (fun i hi => (Finset.mem_filter.mp hi).2)
      exact h1.trans (mul_le_mul_of_nonneg_right hcard hε)
  have hout : ∑ i ∈ (Finset.range T).filter (fun i => i ∉ C), d i ≤
      ∑ i ∈ (Finset.range T).filter (fun i => i ∉ C), |d i| :=
    Finset.sum_le_sum fun i _ => le_abs_self _
  show 1 - δ - (C.card : ℝ) * ε ≤ ∑ i ∈ (Finset.range T).filter (fun i => i ∉ C), |d i|
  linarith

import Mathlib

theorem solution {I : Type} (s : Finset I) (w a b : I → ℝ) (p : ℝ)
    (wn : ∀ i ∈ s, 0 ≤ w i) (left : ∑ i ∈ s, w i * a i^2 ≤ p)
    (right : ∑ i ∈ s, w i * b i^2 ≤ p) : ∑ i ∈ s, w i*(a i*b i) ≤ p := by
  have h : ∑ i ∈ s, (w i * (a i*b i) + w i * (a i*b i)) ≤
      ∑ i ∈ s, (w i*a i^2 + w i*b i^2) := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    nlinarith only [mul_nonneg (wn i hi) (sq_nonneg (a i-b i))]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at h
  linarith

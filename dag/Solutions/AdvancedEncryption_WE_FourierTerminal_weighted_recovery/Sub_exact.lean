import Mathlib

theorem solution {I : Type} (s : Finset I) (w a success : I → ℝ) (wn : ∀ i ∈ s, 0 ≤ w i)
    (ws : ∑ i ∈ s, w i = 1) (ok : ∀ i ∈ s, a i ^ 2 ≤ success i) :
    (∑ i ∈ s, w i * a i)^2 ≤ ∑ i ∈ s, w i * success i := by
  let m := ∑ i ∈ s, w i * a i
  have pos : 0 ≤ ∑ i ∈ s, w i * (a i - m)^2 :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (wn i hi) (sq_nonneg _))
  have expand : (∑ i ∈ s, w i * (a i - m)^2) = (∑ i ∈ s, w i * a i^2) - m^2 := by
    calc
      _ = ∑ i ∈ s, ((w i * a i^2 - (2*m)*(w i*a i)) + m^2*w i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ws]
        change _ - 2*m*m + m^2*1 = _ - m^2
        ring
  rw [expand] at pos
  exact (sub_nonneg.mp pos).trans (Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_left (ok i hi) (wn i hi)))

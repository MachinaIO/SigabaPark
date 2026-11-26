import Mathlib.Analysis.MeanInequalities
open Finset

theorem solution (k : ℕ) (hk : 0 < k) (N : Fin k → ℝ)
    (hN : ∀ i, 0 ≤ N i) (t : ℝ) (ht : 0 ≤ t) (hcov : t ^ k ≤ ∏ i, N i) :
    (k : ℝ) * t ≤ ∑ i, N i := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have amgm := Real.geom_mean_le_arith_mean (univ : Finset (Fin k)) (fun _ => (1 : ℝ)) N
    (fun _ _ => zero_le_one) (by simp [hkpos]) (fun i _ => hN i)
  simp only [Real.rpow_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    one_mul] at amgm
  have h1 : t ≤ (∏ i, N i) ^ ((k : ℝ)⁻¹) := by
    have : t = (t ^ k) ^ ((k : ℝ)⁻¹) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht, mul_inv_cancel₀ hkpos.ne', Real.rpow_one]
    rw [this]
    exact Real.rpow_le_rpow (pow_nonneg ht k) hcov (inv_nonneg.mpr hkpos.le)
  have := h1.trans amgm
  rw [le_div_iff₀ hkpos] at this
  linarith

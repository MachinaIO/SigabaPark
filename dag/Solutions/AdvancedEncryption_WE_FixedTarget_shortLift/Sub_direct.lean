import Definitions.Def_FixedTargetGeometry
open FixedTarget225
theorem solution (q k x y u : ℤ) (hq : 0 < q) (hk : 0 < k)
    (h : k*x-k*y = q*u) (hlo : -q < k*x-k*y) (hhi : k*x-k*y < q) : x=y := by
  have hu : u=0 := by
    rcases lt_trichotomy u 0 with hn|he|hp
    · have h₁ : u≤ -1 := by omega
      have := mul_le_mul_of_nonneg_left h₁ (le_of_lt hq)
      nlinarith
    · exact he
    · have h₁ : 1≤u := by omega
      have := mul_le_mul_of_nonneg_left h₁ (le_of_lt hq)
      nlinarith
  rw [hu,mul_zero,sub_eq_zero] at h
  exact mul_left_cancel₀ (ne_of_gt hk) h

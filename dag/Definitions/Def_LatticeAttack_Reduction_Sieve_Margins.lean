module

public import Definitions.Def_LatticeAttack_Reduction_Sieve_Lens

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Lattices.Sieve

open Real Filter MeasureTheory Metric

/-- In the prescribed axial shell the smaller lens mean dominates n⁵,
uniformly in the radius and the tree level. -/
theorem lensMean_eventually (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, n = k+1 → ∀ i : ℕ, (i:ℝ) ≤ K * log n^3 →
      ∀ R : ℝ, 0 ≤ R →
      let L : ℝ := ⌈log n⌉₊
      let g := 1-1/L
      let w := ((n:ℝ)^2)⁻¹
      let S := axialShell (F:=EuclideanSpace ℝ (Fin k)) R w 0
      let V := volume.real S
      let β := volume.real (S ∩ axialShell R w (g*R))
      (n:ℝ)^5 * V ≤ prescribedSize n i * (g^n * β) := by
  filter_upwards [prescribedSize_reserve K hK 12,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4,
    eventually_ge_atTop 10] with n hsize hl hn
  change 4 ≤ log (n:ℝ) at hl
  intro k hk i hi R hR
  dsimp only
  let L : ℝ := ⌈log n⌉₊
  let g := 1-1/L
  let q := sqrt (1-(g/2)^2)
  let w := ((n:ℝ)^2)⁻¹
  let c := log (4/3)/2
  have hL : 4 ≤ L := hl.trans (Nat.le_ceil _)
  have hp : 0 < L := by linarith
  have hN : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ) < n := by linarith
  have hg : 1/2 ≤ g := by dsimp [g]; rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hp]; linarith
  have hg0 : 0 < g := by linarith
  have hg1 : g ≤ 1 := by dsimp [g]; linarith [one_div_pos.mpr hp]
  have hq0 : 0 ≤ 1-(g/2)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hg1) (by linarith : 0 ≤ 1+g)]
  have hq := Real.sq_sqrt hq0
  change q^2 = _ at hq
  have hqc : 1 ≤ exp c * q := by
    have hexp : (exp c)^2 = 4/3 := by rw [← exp_nat_mul]; push_cast; rw [show 2*c = log (4/3) by dsimp [c]; ring, exp_log (by norm_num)]
    have hsq : (exp c * q)^2 ≥ 1 := by
      rw [mul_pow, hexp, hq]
      nlinarith [mul_nonneg (sub_nonneg.mpr hg1) (by linarith : 0 ≤ 1+g)]
    have hnon : 0 ≤ exp c * q := mul_nonneg (exp_pos _).le (sqrt_nonneg _)
    nlinarith
  have hglog : -(3/(2*L)) ≤ log g := by
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hg0)
    rw [log_inv] at hh
    have H : g⁻¹ ≤ 1+3/(2*L) := by
      rw [inv_le_iff_one_le_mul₀ hg0]
      dsimp [g]; field_simp; linarith
    linarith
  have hcq : 1 ≤ exp (c*n)*q^k := by
    have HH := one_le_pow₀ (n:=k) hqc
    rw [mul_pow, ← exp_nat_mul] at HH
    apply HH.trans
    apply mul_le_mul_of_nonneg_right (exp_le_exp.mpr ?_) (pow_nonneg (sqrt_nonneg _) _)
    rw [hk]; push_cast; dsimp [c]; nlinarith [show 0 ≤ log (4/3:ℝ) by positivity]
  have hgg : 1 ≤ exp (3*n/(2*L))*g^n := by
    conv_rhs => rhs; rw [← exp_log hg0, ← exp_nat_mul]
    rw [← exp_add, one_le_exp_iff]
    rw [show 3*(n:ℝ)/(2*L) = n*(3/(2*L)) by ring]
    nlinarith [mul_le_mul_of_nonneg_left hglog (Nat.cast_nonneg n)]
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hw' : w ≤ 1 := by dsimp [w]; rw [inv_le_one₀ (by positivity)]; nlinarith
  have hwN : (1+w)^n ≤ (n:ℝ) := by
    have hh : (n:ℝ)*w ≤ 1 := by dsimp [w]; rw [← div_eq_mul_inv, div_le_one (by positivity)]; nlinarith
    calc
      _ ≤ (exp w)^n := by gcongr; linarith [add_one_le_exp w]
      _ ≤ exp (log n) := by rw [← exp_nat_mul]; exact exp_le_exp.mpr (by linarith)
      _ = _ := exp_log hnp
  let S := axialShell (F:=EuclideanSpace ℝ (Fin k)) R w 0
  let V := volume.real S
  let β := volume.real (S ∩ axialShell R w (g*R))
  have hlens := lensVolume_relative (k:=k) (by omega) hR hw hw' hg0.le (sqrt_nonneg _) (by linarith : (g/2)^2+q^2=1)
  change w^2*g*q^k*V ≤ 2*(1+w)^(k+1)*β at hlens
  rw [← hk] at hlens
  have hβ : 0 ≤ β := measureReal_nonneg
  have hV : 0 ≤ V := measureReal_nonneg
  have hscale : (n:ℝ)^12 * w^2 = (n:ℝ)^8 := by dsimp [w]; field_simp
  have hpoly : 2*(n:ℝ)*n^5 ≤ n^8*g := by
    have hh' : 2 ≤ (n:ℝ)^2 * g := by nlinarith [mul_le_mul_of_nonneg_left hg (sq_nonneg (n:ℝ))]
    nlinarith only [mul_le_mul_of_nonneg_left hh' (pow_nonneg hnp.le 6)]
  have hbound := mul_le_mul_of_nonneg_left (hlens.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hwN (by norm_num)) hβ))
    (show 0 ≤ (n:ℝ)^12 * exp (c*n) * (exp (3*n/(2*L))*g^n) by positivity)
  have hm := hsize i hi
  change (n:ℝ)^12 * exp _ ≤ _ at hm
  rw [exp_add, show log (4/3)*(n:ℝ)/2 = c*n by dsimp [c]; ring] at hm
  change (n:ℝ)^5 * V ≤ _ * (g^n*β)
  apply le_of_mul_le_mul_left (a:=2*(n:ℝ)) _ (by positivity)
  calc
    _ ≤ (n:ℝ)^8*g*V := by rw [← mul_assoc]; gcongr
    _ ≤ ((n:ℝ)^8*g*V) * ((exp (c*n)*q^k)*(exp (3*n/(2*L))*g^n)) :=
      le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hcq hgg)
    _ = _ := by rw [← hscale]; ring
    _ ≤ _ := hbound
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_right hm (show 0 ≤ 2*(n:ℝ)*(g^n*β) by positivity) using 1 <;> ring

#print axioms lensMean_eventually

end SigabaNeo.Lattices.Sieve

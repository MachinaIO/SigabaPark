module

public import Mathlib

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Lattices.Sieve

open Finset Real Filter

/-- Exponential tilting for an indexed uniform bank, counting repetitions. -/
theorem bankTilt {G : Type*} [DecidableEq G] (U : Finset G) (P : G → Prop)
    [DecidablePred P] (M : ℕ) (t z : ℝ) (hU : 0 < (U.card : ℝ)) :
    let B := Fintype.piFinset fun _ : Fin M ↦ U
    let X := fun C : Fin M → G ↦ (univ.filter fun j ↦ P (C j)).card
    (((B.filter fun C ↦ z ≤ t * X C).card : ℝ)) ≤
      (U.card : ℝ)^M * exp (M * ((U.filter P).card / (U.card : ℝ)) * (exp t - 1) - z) := by
  classical
  dsimp only
  let B := Fintype.piFinset fun _ : Fin M ↦ U
  let X := fun C : Fin M → G ↦ (univ.filter fun j ↦ P (C j)).card
  let w := fun c ↦ if P c then exp t else 1
  have prodW (C : Fin M → G) : ∏ j, w (C j) = exp (t * X C) := by
    simp [w, X, ← prod_filter, ← Real.exp_nat_mul, mul_comm]
  have sumW : ∑ c ∈ U, w c = U.card + (U.filter P).card * (exp t - 1) := by
    calc
      _ = ∑ c ∈ U, (1 + (if P c then exp t - 1 else 0)) := by
        apply sum_congr rfl
        intro c _
        by_cases h : P c <;> simp [w,h]
      _ = _ := by simp [sum_add_distrib, ← sum_filter, nsmul_eq_mul, mul_sub]
  let a := (U.filter P).card / (U.card : ℝ) * (exp t - 1)
  have hw : ∑ c ∈ U, w c ≤ U.card * exp a := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp a) hU.le
    rw [sumW]
    dsimp [a] at *
    field_simp [hU.ne'] at *
    linarith
  change ((B.filter fun C ↦ z ≤ t * X C).card : ℝ) ≤ _
  rw [Real.exp_sub, ← mul_div_assoc, le_div_iff₀ (Real.exp_pos z)]
  calc
    _ = ∑ _C ∈ B.filter (fun C ↦ z ≤ t * X C), exp z := by simp [nsmul_eq_mul]
    _ ≤ ∑ C ∈ B.filter (fun C ↦ z ≤ t * X C), ∏ j, w (C j) := by
      exact sum_le_sum fun C h ↦ (prodW C).symm ▸ exp_le_exp.mpr (mem_filter.mp h).2
    _ ≤ ∑ C ∈ B, ∏ j, w (C j) := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun C _ _ ↦ (prodW C).symm ▸ (exp_pos _).le
    _ = (∑ c ∈ U, w c)^M := (sum_pow' U w M).symm
    _ ≤ (U.card * exp a)^M := by
      apply pow_le_pow_left₀ _ hw
      exact sum_nonneg fun c _ ↦ by dsimp [w]; split <;> positivity
    _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; congr 2; dsimp [a]; ring

/-- Upper and lower multiplicative Chernoff counts, scaled by the expected lens size. -/
theorem bankLensTails {G : Type*} [DecidableEq G] (U : Finset G) (P : G → Prop)
    [DecidablePred P] (M : ℕ) (a : ℝ) (hU : 0 < (U.card : ℝ)) (ha : 0 ≤ a)
    (hhi : M * ((U.filter P).card / (U.card : ℝ)) ≤ 203/100*a)
    (hlo : 33/100*a ≤ M * ((U.filter P).card / (U.card : ℝ))) :
    let B := Fintype.piFinset fun _ : Fin M ↦ U
    let X := fun C : Fin M → G ↦ (univ.filter fun j ↦ P (C j)).card
    (((B.filter fun C ↦ 3*a < X C).card : ℝ) ≤ U.card^M * exp (-a/120)) ∧
    (((B.filter fun C ↦ (X C : ℝ) < a/4).card : ℝ) ≤ U.card^M * exp (-a/240)) := by
  classical
  dsimp only
  constructor
  · let t := log (5/4)
    have ht : 1/5 ≤ t := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (5/4:ℝ)⁻¹)
      rw [Real.log_inv] at h
      dsimp [t]; linarith
    apply le_trans _ ((bankTilt U P M t (t*(3*a)) hU).trans ?_)
    · apply Nat.cast_le.mpr (card_le_card ?_)
      intro C h
      exact mem_filter.mpr ⟨(mem_filter.mp h).1,
        mul_le_mul_of_nonneg_left (mem_filter.mp h).2.le (by linarith)⟩
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply exp_le_exp.mpr
      rw [show exp t = 5/4 from Real.exp_log (by norm_num)]
      nlinarith [mul_le_mul_of_nonneg_right ht ha]
  · let t := log (7/8)
    have ht : -(1/7) ≤ t := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (7/8:ℝ)⁻¹)
      rw [Real.log_inv] at h
      dsimp [t]; linarith
    have ht' : t ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    apply le_trans _ ((bankTilt U P M t (t*(a/4)) hU).trans ?_)
    · apply Nat.cast_le.mpr (card_le_card ?_)
      intro C h
      exact mem_filter.mpr ⟨(mem_filter.mp h).1,
        mul_le_mul_of_nonpos_left (mem_filter.mp h).2.le ht'⟩
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply exp_le_exp.mpr
      rw [show exp t = 7/8 from Real.exp_log (by norm_num)]
      nlinarith [mul_le_mul_of_nonneg_right ht ha]

noncomputable def prescribedSize (n : ℕ) : ℕ → ℕ
  | 0 => ⌈exp (log (4/3) * n / 2 + 2*n / (⌈log n⌉₊ : ℝ))⌉₊
  | i+1 => prescribedSize n i / 16

theorem prescribedSize_le (n i : ℕ) : prescribedSize n i ≤ prescribedSize n 0 := by
  induction i with
  | zero => rfl
  | succ i ih => exact (Nat.div_le_self _ _).trans ih

/-- Flooring the successive list sizes loses less than one unit after rescaling. -/
theorem prescribedSize_rounding (n i : ℕ) :
    prescribedSize n 0 < (prescribedSize n i + 1) * 16^i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have step : prescribedSize n i + 1 ≤ (prescribedSize n (i+1)+1)*16 := by
      change prescribedSize n i + 1 ≤ (prescribedSize n i / 16 + 1)*16
      omega
    rw [pow_succ]
    exact ih.trans_le (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_right (16^i) step)

/-- The prescribed list sizes absorb the cubic-log tree depth and the mover tail target. -/
theorem prescribedSize_eventually (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, (i:ℝ) ≤ K*log n^3 →
      1000*((n:ℝ)/log n) ≤ prescribedSize n i := by
  let c := log (4/3)/2
  have hc : 0 < c := by dsimp [c]; positivity
  let a := c/(K*log 16+3)
  have ha : 0 < a := by dsimp [a]; positivity
  have small := (Real.isLittleO_pow_log_id_atTop (n := 3)).bound ha
  filter_upwards [tendsto_natCast_atTop_atTop.eventually small,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 10,
    eventually_ge_atTop 1001] with n hn hl hn'
  change 10 ≤ log (n:ℝ) at hl
  change ‖log (n:ℝ)^3‖ ≤ a * ‖(n:ℝ)‖ at hn
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ log (n:ℝ)^3),
    abs_of_nonneg (show 0 ≤ (n:ℝ) by positivity)] at hn
  intro i hi
  have h3 : log (n:ℝ) ≤ log (n:ℝ)^3 := by
    have h := pow_le_pow_right₀ (by linarith : 1 ≤ log (n:ℝ)) (by decide : 1 ≤ 3)
    simpa using h
  have bound : (K*log 16 + 3)*log (n:ℝ)^3 ≤ c*n := by
    dsimp [a] at hn
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hn
    linarith
  have hbase : ((n:ℝ)^2) * (16:ℝ)^i ≤ (prescribedSize n 0 : ℝ) := by
    change _ ≤ (⌈exp _⌉₊ : ℝ)
    apply le_trans _ (Nat.le_ceil _)
    have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [← Real.exp_log hnpos, ← Real.exp_log (by norm_num : (0:ℝ) < 16),
      ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    simp only [Real.exp_log hnpos]
    apply exp_le_exp.mpr
    dsimp [c] at bound
    have hr : 0 ≤ 2*(n:ℝ)/(⌈log n⌉₊ : ℝ) := by positivity
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hi (show 0 ≤ log (16:ℝ) by positivity)]
  have hround : (prescribedSize n 0 : ℝ) < ((prescribedSize n i : ℝ)+1)*(16:ℝ)^i := by
    exact_mod_cast prescribedSize_rounding n i
  have hlower := lt_of_mul_lt_mul_right (hbase.trans_lt hround) (by positivity : (0:ℝ) ≤ 16^i)
  have hdiv : (n:ℝ)/log n ≤ n := (div_le_self (by positivity) (by linarith))
  have hnreal : (1001:ℝ) ≤ n := by exact_mod_cast hn'
  nlinarith [mul_nonneg (show 0 ≤ (n:ℝ)-1001 by linarith) (show 0 ≤ (n:ℝ) by positivity)]

/-- The right side of the exhaustive comparison bound at the prescribed parameters. -/
theorem prescribedBudget (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (m : ℝ) ≤ K * log n ^ 3 →
      let B := prescribedSize n 0
      ((m * (2^m * (2*B*B)) + B^2 : ℕ) : ℝ) ≤
        (4/3 : ℝ)^n * exp ((2*K+8)*n/log n) := by
  have small := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound (show (0:ℝ) < 1 by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually small,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1] with n hn hl
  change 1 ≤ log (n : ℝ) at hl
  change ‖log (n : ℝ)^4‖ ≤ 1 * ‖(n : ℝ)‖ at hn
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ log (n : ℝ)^4),
    abs_of_nonneg (show 0 ≤ (n:ℝ) by positivity), one_mul] at hn
  intro m hm
  dsimp only
  let x := log (4/3) * n / 2 + 2*n / (⌈log n⌉₊ : ℝ)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hB : (prescribedSize n 0 : ℝ) ≤ 2 * exp x := by
    change (⌈exp x⌉₊ : ℝ) ≤ _
    linarith [Nat.ceil_lt_add_one (exp_pos x).le, Real.add_one_le_exp x]
  have h2 : (2:ℝ)^m ≤ exp m := by
    rw [show (m:ℝ) = m*1 by ring, Real.exp_nat_mul]
    gcongr
    linarith [Real.add_one_le_exp (1:ℝ)]
  have hm' : (m:ℝ) ≤ exp m := by linarith [Real.add_one_le_exp (m:ℝ)]
  have hL : 2*(n:ℝ) / (⌈log n⌉₊ : ℝ) ≤ 2*n/log n :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (Nat.le_ceil _)
  have hpoly : log (n:ℝ)^3 ≤ n / log n := (le_div_iff₀ (by linarith)).2 (by nlinarith only [hn])
  have hunit : 1 ≤ (n:ℝ) / log n := le_trans (one_le_pow₀ hl) hpoly
  have hm2 : (m:ℝ) ≤ K * (n/log n) := hm.trans (mul_le_mul_of_nonneg_left hpoly hK)
  push_cast
  calc
    _ ≤ exp m * (exp m * (2*(2*exp x)*(2*exp x))) + (2*exp x)^2 := by gcongr
    _ ≤ 12 * exp (2*m+2*x) := by
      rw [show 2*(m:ℝ)+2*x = m+m+(x+x) by ring]
      simp only [Real.exp_add]
      have he : 1 ≤ exp (m:ℝ) := Real.one_le_exp (by positivity)
      nlinarith [mul_nonneg (sq_nonneg (exp x))
        (sub_nonneg.mpr (one_le_mul_of_one_le_of_one_le he he))]
    _ ≤ exp (4 + (2*m+2*x)) := by
      rw [Real.exp_add 4]
      gcongr
      have he : (2:ℝ) ≤ exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) he 4
      rw [← Real.exp_nat_mul] at hh
      norm_num at hh
      linarith
    _ ≤ _ := by
      rw [← Real.exp_log (by norm_num : (0:ℝ) < 4/3), ← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp [x]
      rw [add_mul, add_div]
      linarith [show 2*(n:ℝ)/log n = 2*(n/log n) by ring, show 2*K*(n:ℝ)/log n = 2*(K*(n/log n)) by ring,
        show 8*(n:ℝ)/log n = 8*(n/log n) by ring]

/-- A cubic-log tree has enough margin in the dimension-only union bound. -/
theorem treeOverhead_eventually (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, (i:ℝ) ≤ K*log n^3 →
      4*(2:ℝ)^i+2 ≤ exp ((n/log n)/2) := by
  have ha : 0 < (1:ℝ)/(2*(K+3)) := by positivity
  have small := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound ha
  filter_upwards [tendsto_natCast_atTop_atTop.eventually small,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1] with n hn hl
  change 1 ≤ log (n:ℝ) at hl
  change ‖log (n:ℝ)^4‖ ≤ _ * ‖(n:ℝ)‖ at hn
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ log (n:ℝ)^4),
    abs_of_nonneg (show 0 ≤ (n:ℝ) by positivity)] at hn
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hn
  intro i hi
  have h3 : 1 ≤ log (n:ℝ)^3 := one_le_pow₀ hl
  have hsum : 3+i ≤ (K+3)*log (n:ℝ)^3 := by linarith
  have hx : (3+(i:ℝ)) ≤ (n/log n)/2 := by
    apply (le_div_iff₀ (by norm_num)).2
    apply (le_div_iff₀ (by linarith)).2
    nlinarith only [hn, mul_le_mul_of_nonneg_right hsum (by linarith : 0 ≤ log (n:ℝ))]
  have h2 : (2:ℝ) ≤ exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have h8 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h2 3
  rw [← Real.exp_nat_mul] at h8
  norm_num at h8
  have hpow : (2:ℝ)^i ≤ exp i := by
    simpa [← Real.exp_nat_mul] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h2 i
  apply le_trans _ (exp_le_exp.mpr hx)
  rw [exp_add]
  nlinarith [mul_le_mul_of_nonneg_right h8 (exp_pos (i:ℝ)).le,
    one_le_pow₀ (n := i) (by norm_num : (1:ℝ) ≤ 2)]

#print axioms treeOverhead_eventually
#print axioms prescribedSize_eventually
#print axioms prescribedBudget
#print axioms bankLensTails
#print axioms bankTilt

end SigabaNeo.Lattices.Sieve

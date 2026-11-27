module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit true

/-!
# One-dimensional Gaussian smoothing (Wall 1, Part 141 Lemma 2)

* `theta1 s c = ∑ₖ exp (-π (k + c)² / s²)` is the Gaussian mass `ρ_s(ℤ + c)`.
* `theta1_poisson`: `ρ_s(ℤ + c) = s · ∑ₖ exp (-π s² k²) cos (2π k c)` (Poisson summation).
* `tailSum a = ∑_{k ≥ 1} exp (-a k²)` and `tau s = 2 · tailSum (π s²)`.
* `abs_theta1_div_sub_one_le`: `|ρ_s(ℤ + c)/s - 1| ≤ tau s`.
* `tailSum_le`: `tailSum a ≤ e^{-a} / (1 - e^{-3a})`.
* `thetaQ s q c = ρ_s(qℤ + c)` and its bound with ratio `s/q`.
* `klein_ratio_bounds`, `klein_sd_le`: the Klein-vs-`D_{L,s}` comparison of Lemma 2, in the
  factorized form given by Lemma 1.
-/

public section

namespace SigabaNeo.Wall1

open Real

noncomputable section

/-- The one-dimensional Gaussian theta function `ρ_s(ℤ + c)`. -/
def theta1 (s c : ℝ) : ℝ := ∑' k : ℤ, Real.exp (-π * ((k : ℝ) + c) ^ 2 / s ^ 2)

/-- `∑_{k ≥ 1} exp (-a k²)`. -/
def tailSum (a : ℝ) : ℝ := ∑' n : ℕ, Real.exp (-a * ((n : ℝ) + 1) ^ 2)

/-- The smoothing error `τ(s) = 2 ∑_{k ≥ 1} exp (-π s² k²)`. -/
def tau (s : ℝ) : ℝ := 2 * tailSum (π * s ^ 2)

/-! ### Geometric domination -/

private theorem exp_sq_le_geom {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    Real.exp (-a * ((n : ℝ) + 1) ^ 2) ≤ Real.exp (-a) * Real.exp (-3 * a) ^ n := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hn ha]

private theorem exp_sq_le_geom0 {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    Real.exp (-a * (n : ℝ) ^ 2) ≤ Real.exp (-a) ^ n := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hn ha]

private theorem summable_geom_exp {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ ↦ Real.exp (-a) ^ n) :=
  summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))

theorem summable_tail {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ ↦ Real.exp (-a * ((n : ℝ) + 1) ^ 2)) := by
  have hg : Summable (fun n : ℕ ↦ Real.exp (-3 * a) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
  exact Summable.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le) (exp_sq_le_geom ha.le)
    (hg.mul_left (Real.exp (-a)))

theorem tailSum_nonneg (a : ℝ) : 0 ≤ tailSum a :=
  tsum_nonneg fun _ ↦ (Real.exp_pos _).le

/-- `∑_{k ≥ 1} e^{-a k²} ≤ e^{-a} / (1 - e^{-3a})`. -/
theorem tailSum_le {a : ℝ} (ha : 0 < a) :
    tailSum a ≤ Real.exp (-a) / (1 - Real.exp (-3 * a)) := by
  have hr : Real.exp (-3 * a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg := summable_geometric_of_lt_one (Real.exp_pos (-3 * a)).le hr
  calc tailSum a ≤ ∑' n : ℕ, Real.exp (-a) * Real.exp (-3 * a) ^ n :=
        (summable_tail ha).tsum_le_tsum (exp_sq_le_geom ha.le) (hg.mul_left _)
    _ = Real.exp (-a) / (1 - Real.exp (-3 * a)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hr, div_eq_mul_inv]

/-- The integer Gaussian `k ↦ exp (-a k²)` is summable over `ℤ`. -/
theorem summable_int_gauss {a : ℝ} (ha : 0 < a) :
    Summable (fun k : ℤ ↦ Real.exp (-a * (k : ℝ) ^ 2)) := by
  have h0 : Summable (fun n : ℕ ↦ Real.exp (-a * (n : ℝ) ^ 2)) :=
    Summable.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le) (exp_sq_le_geom0 ha.le)
      (summable_geom_exp ha)
  refine Summable.of_nat_of_neg_add_one (by simpa using h0) ?_
  refine (summable_tail ha).congr fun n ↦ ?_
  push_cast; ring_nf

/-! ### Poisson summation -/

/-- **Poisson summation for the 1-D Gaussian.**
`ρ_s(ℤ + c) = s · ∑ₖ exp (-π s² k²) · cos (2π k c)`. -/
theorem theta1_poisson {s : ℝ} (hs : 0 < s) (c : ℝ) :
    theta1 s c = s * ∑' k : ℤ, Real.exp (-π * s ^ 2 * (k : ℝ) ^ 2) * Real.cos (2 * π * k * c) := by
  have hs2 : 0 < ((s ^ 2 : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; positivity
  have h := Complex.tsum_exp_neg_quadratic hs2 (-(Complex.I * c))
  have hI : Complex.I * -(Complex.I * (c : ℂ)) = c := by
    rw [mul_neg, ← mul_assoc, Complex.I_mul_I]; ring
  rw [hI] at h
  have hsqrt : ((s ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = s := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hs.le]
  rw [hsqrt] at h
  -- right-hand side is `(1/s) · theta1 s c`
  have hR : (∑' n : ℤ, Complex.exp (-π / ((s ^ 2 : ℝ) : ℂ) * ((n : ℂ) + c) ^ 2)) =
      ((theta1 s c : ℝ) : ℂ) := by
    rw [theta1, Complex.ofReal_tsum]
    refine tsum_congr fun n ↦ ?_
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [hR] at h
  -- left-hand side: real parts
  set F : ℤ → ℂ := fun n ↦ Complex.exp (-π * ((s ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ 2 +
    2 * π * -(Complex.I * c) * n) with hF
  have hnorm (n : ℤ) : ‖F n‖ = Real.exp (-(π * s ^ 2) * (n : ℝ) ^ 2) := by
    rw [hF, Complex.norm_exp]; congr 1
    simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_intCast, sq]
  have hsum : Summable F :=
    Summable.of_norm (by simpa only [hnorm] using summable_int_gauss (by positivity))
  have hre (n : ℤ) : (F n).re = Real.exp (-π * s ^ 2 * (n : ℝ) ^ 2) * Real.cos (2 * π * n * c) := by
    rw [hF, Complex.exp_re]
    congr 1
    · congr 1; simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_intCast, sq]
    · rw [← Real.cos_neg]; congr 1
      simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_intCast, sq]; ring
  have key := congrArg Complex.re h
  rw [Complex.re_tsum hsum] at key
  simp only [hre] at key
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [show (1 : ℂ) / s * ((theta1 s c : ℝ) : ℂ) = ((theta1 s c / s : ℝ) : ℂ) by
    push_cast; field_simp, Complex.ofReal_re] at key
  rw [key]; field_simp

/-! ### The smoothing bound -/

/-- `ρ_s(ℤ + c)/s - 1 = 2 ∑_{k ≥ 1} e^{-π s² k²} cos (2π k c)`. -/
theorem theta1_div_sub_one {s : ℝ} (hs : 0 < s) (c : ℝ) :
    theta1 s c / s - 1 =
      2 * ∑' n : ℕ, Real.exp (-(π * s ^ 2) * ((n : ℝ) + 1) ^ 2) *
        Real.cos (2 * π * ((n : ℝ) + 1) * c) := by
  set a := π * s ^ 2 with ha_def
  have ha : 0 < a := by positivity
  set f : ℤ → ℝ := fun k ↦ Real.exp (-π * s ^ 2 * (k : ℝ) ^ 2) * Real.cos (2 * π * k * c)
    with hf
  have hbound (k : ℤ) : ‖f k‖ ≤ Real.exp (-a * (k : ℝ) ^ 2) := by
    rw [hf, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), ha_def, neg_mul]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  have hfs : Summable f := Summable.of_norm_bounded (summable_int_gauss ha) hbound
  set g : ℕ → ℝ := fun n ↦ Real.exp (-(π * s ^ 2) * ((n : ℝ) + 1) ^ 2) *
    Real.cos (2 * π * ((n : ℝ) + 1) * c) with hg
  have hneg : (fun n : ℕ ↦ f (-((n : ℤ) + 1))) = g := by
    funext n; rw [hf, hg]; push_cast
    rw [← Real.cos_neg]; congr 2 <;> ring
  have hnat : Summable (fun n : ℕ ↦ f (n : ℤ)) := hfs.comp_injective Nat.cast_injective
  have hnat' : Summable (fun n : ℕ ↦ f (-((n : ℤ) + 1))) :=
    hfs.comp_injective (fun a b h ↦ by simpa using h)
  have hsplit := tsum_of_nat_of_neg_add_one hnat hnat'
  rw [hneg] at hsplit
  have hshift : (∑' n : ℕ, f (n : ℤ)) = f 0 + ∑' n : ℕ, g n := by
    rw [hnat.tsum_eq_zero_add]
    congr 1
    refine tsum_congr fun n ↦ ?_
    rw [hf, hg]; push_cast; ring_nf
  have hf0 : f 0 = 1 := by simp [hf]
  rw [theta1_poisson hs c]
  change s * (∑' k : ℤ, f k) / s - 1 = 2 * ∑' n : ℕ, g n
  rw [hsplit, hshift, hf0]
  field_simp
  ring

/-- **Smoothing bound.** For every real `c`, `|ρ_s(ℤ + c)/s - 1| ≤ τ(s)`. -/
theorem abs_theta1_div_sub_one_le {s : ℝ} (hs : 0 < s) (c : ℝ) :
    |theta1 s c / s - 1| ≤ tau s := by
  have ha : 0 < π * s ^ 2 := by positivity
  rw [theta1_div_sub_one hs c, tau, tailSum, abs_mul, abs_two]
  gcongr
  have hb (n : ℕ) : ‖Real.exp (-(π * s ^ 2) * ((n : ℝ) + 1) ^ 2) *
      Real.cos (2 * π * ((n : ℝ) + 1) * c)‖ ≤ Real.exp (-(π * s ^ 2) * ((n : ℝ) + 1) ^ 2) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  have := tsum_of_norm_bounded (summable_tail ha).hasSum hb
  simpa [Real.norm_eq_abs] using this

/-- The explicit form: `τ(s) ≤ 2 e^{-π s²} / (1 - e^{-3π s²})`. -/
theorem tau_le {s : ℝ} (hs : 0 < s) :
    tau s ≤ 2 * Real.exp (-(π * s ^ 2)) / (1 - Real.exp (-3 * (π * s ^ 2))) := by
  rw [tau, mul_div_assoc]
  gcongr
  exact tailSum_le (by positivity)

theorem tau_nonneg (s : ℝ) : 0 ≤ tau s := mul_nonneg zero_le_two (tailSum_nonneg _)

/-- Two-sided form: `s (1 - τ) ≤ ρ_s(ℤ + c) ≤ s (1 + τ)`. -/
theorem theta1_mem {s : ℝ} (hs : 0 < s) (c : ℝ) :
    s * (1 - tau s) ≤ theta1 s c ∧ theta1 s c ≤ s * (1 + tau s) := by
  have h := abs_le.mp (abs_theta1_div_sub_one_le hs c)
  have e : theta1 s c = s * (theta1 s c / s) := by field_simp
  constructor
  · rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) hs.le
  · rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) hs.le

/-! ### Cosets `qℤ + c` -/

/-- `ρ_s(qℤ + c) = ∑ₖ exp (-π (q k + c)² / s²)`. -/
def thetaQ (s q c : ℝ) : ℝ := ∑' k : ℤ, Real.exp (-π * (q * (k : ℝ) + c) ^ 2 / s ^ 2)

theorem thetaQ_eq {s q : ℝ} (hq : q ≠ 0) (c : ℝ) : thetaQ s q c = theta1 (s / q) (c / q) := by
  unfold thetaQ theta1
  refine tsum_congr fun k ↦ ?_
  congr 1
  field_simp

/-- **Coset smoothing bound** (Gram–Schmidt norm `q`):
`|ρ_s(qℤ + c) / (s/q) - 1| ≤ τ(s/q)`. -/
theorem abs_thetaQ_div_sub_one_le {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (c : ℝ) :
    |thetaQ s q c / (s / q) - 1| ≤ tau (s / q) := by
  rw [thetaQ_eq hq.ne']; exact abs_theta1_div_sub_one_le (div_pos hs hq) _

theorem thetaQ_mem {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (c : ℝ) :
    (s / q) * (1 - tau (s / q)) ≤ thetaQ s q c ∧ thetaQ s q c ≤ (s / q) * (1 + tau (s / q)) := by
  rw [thetaQ_eq hq.ne']; exact theta1_mem (div_pos hs hq) _

/-! ### Ratio lemmas -/

/-- Per-coordinate ratio lemma: two quantities within relative error `τ < 1` of the same
`m > 0` have ratio in `[(1-τ)/(1+τ), (1+τ)/(1-τ)]`. -/
theorem ratio_mem {m τ x y : ℝ} (hm : 0 < m) (hτ : τ < 1)
    (hx : |x / m - 1| ≤ τ) (hy : |y / m - 1| ≤ τ) :
    (1 - τ) / (1 + τ) ≤ x / y ∧ x / y ≤ (1 + τ) / (1 - τ) := by
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  have hτ0 : 0 ≤ τ := (abs_nonneg _).trans hx
  have hxy : x / y = (x / m) / (y / m) := by
    rw [div_div_div_cancel_right₀ hm.ne']
  have hyp : 0 < y / m := by linarith
  rw [hxy]
  constructor
  · rw [div_le_div_iff₀ (by linarith) hyp]; nlinarith
  · rw [div_le_div_iff₀ hyp (by linarith)]; nlinarith

/-- Coset ratio: for all centres `c, c'`, `ρ_s(qℤ + c) / ρ_s(qℤ + c')` lies in
`[(1-τ)/(1+τ), (1+τ)/(1-τ)]` with `τ = τ(s/q) < 1`. -/
theorem thetaQ_ratio_mem {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (hτ : tau (s / q) < 1) (c c' : ℝ) :
    (1 - tau (s / q)) / (1 + tau (s / q)) ≤ thetaQ s q c / thetaQ s q c' ∧
      thetaQ s q c / thetaQ s q c' ≤ (1 + tau (s / q)) / (1 - tau (s / q)) :=
  ratio_mem (div_pos hs hq) hτ (abs_thetaQ_div_sub_one_le hs hq c)
    (abs_thetaQ_div_sub_one_le hs hq c')

/-! ### Klein versus `D_{L,s}` (Part 141 Lemma 2, factorized form)

On `L_M = {(h,u) : h ≡ M u (mod q)}` with the basis whose Gram–Schmidt norms are `q` (head, `r`
coordinates) and `1` (tail), Lemma 1 of Part 141 factors both laws as
`K(h,u) = p(u) · c(h | u)` and `D_{L,s}(h,u) = p(u) · g(u) / E_p[g] · c(h | u)`,
where `p = D_{ℤ,s}^{⊗t}` is the Klein marginal of the tail, `c(h | u) = ∏ᵢ D_{qℤ + wᵢ(u), s}(hᵢ)`
is the common conditional law, and `g(u) = ∏ᵢ ρ_s(qℤ + wᵢ(u)) / (s/q)`.
Hence `K(h,u) / D_{L,s}(h,u) = E_p[g] / g(u)`; the theorems below bound this ratio and the
statistical distance `½ E_p |g / E_p g - 1|`, for an arbitrary probability `p` and arbitrary
real centres `w`. -/

/-- The Klein correction weight `g(w) = ∏ᵢ ρ_s(qℤ + wᵢ) / (s/q)`. -/
def kleinWeight {r : ℕ} (s q : ℝ) (w : Fin r → ℝ) : ℝ := ∏ i, thetaQ s q (w i) / (s / q)

theorem kleinWeight_mem {r : ℕ} {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (hτ : tau (s / q) < 1)
    (w : Fin r → ℝ) :
    (1 - tau (s / q)) ^ r ≤ kleinWeight s q w ∧ kleinWeight s q w ≤ (1 + tau (s / q)) ^ r := by
  have hm : 0 < s / q := div_pos hs hq
  have hi (i : Fin r) : 1 - tau (s / q) ≤ thetaQ s q (w i) / (s / q) ∧
      thetaQ s q (w i) / (s / q) ≤ 1 + tau (s / q) := by
    have := abs_le.mp (abs_thetaQ_div_sub_one_le hs hq (w i))
    constructor <;> linarith [this.1, this.2]
  unfold kleinWeight
  constructor
  · calc (1 - tau (s / q)) ^ r = ∏ _i : Fin r, (1 - tau (s / q)) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ ↦ by linarith) (fun i _ ↦ (hi i).1)
  · calc _ ≤ ∏ _i : Fin r, (1 + tau (s / q)) :=
          Finset.prod_le_prod₀ (fun i _ ↦ by linarith [(hi i).1]) (fun i _ ↦ (hi i).2)
      _ = (1 + tau (s / q)) ^ r := by simp

/-- Abstract ratio lemma: if `a ≤ g ≤ b` with `a > 0` and `p` is a probability, then
`a/b ≤ E_p[g] / g(u) ≤ b/a`. -/
theorem expect_ratio_mem {α : Type*} {p g : α → ℝ} {a b : ℝ} (hp0 : ∀ u, 0 ≤ p u)
    (hp1 : HasSum p 1) (ha : 0 < a) (hg : ∀ u, a ≤ g u ∧ g u ≤ b) (u : α) :
    a / b ≤ (∑' v, p v * g v) / g u ∧ (∑' v, p v * g v) / g u ≤ b / a := by
  have hab : a ≤ b := (hg u).1.trans (hg u).2
  have hb : 0 < b := ha.trans_le hab
  have hs : Summable (fun v ↦ p v * g v) :=
    Summable.of_nonneg_of_le (fun v ↦ mul_nonneg (hp0 v) (ha.le.trans (hg v).1))
      (fun v ↦ mul_le_mul_of_nonneg_left (hg v).2 (hp0 v)) (hp1.summable.mul_right b)
  have hE1 : a ≤ ∑' v, p v * g v := by
    calc a = ∑' v, p v * a := by rw [tsum_mul_right, hp1.tsum_eq, one_mul]
      _ ≤ _ := (hp1.summable.mul_right a).tsum_le_tsum
          (fun v ↦ mul_le_mul_of_nonneg_left (hg v).1 (hp0 v)) hs
  have hE2 : ∑' v, p v * g v ≤ b := by
    calc _ ≤ ∑' v, p v * b := hs.tsum_le_tsum
          (fun v ↦ mul_le_mul_of_nonneg_left (hg v).2 (hp0 v)) (hp1.summable.mul_right b)
      _ = b := by rw [tsum_mul_right, hp1.tsum_eq, one_mul]
  have hgu : 0 < g u := ha.trans_le (hg u).1
  constructor
  · rw [div_le_div_iff₀ hb hgu]; nlinarith [(hg u).2]
  · rw [div_le_div_iff₀ hgu ha]; nlinarith [(hg u).1]

/-- Abstract statistical-distance lemma: `E_p |g / E_p g - 1| ≤ b/a - 1`. -/
theorem expect_abs_sub_le {α : Type*} {p g : α → ℝ} {a b : ℝ} (hp0 : ∀ u, 0 ≤ p u)
    (hp1 : HasSum p 1) (ha : 0 < a) (hg : ∀ u, a ≤ g u ∧ g u ≤ b) :
    ∑' v, p v * |g v / (∑' w, p w * g w) - 1| ≤ b / a - 1 := by
  set E := ∑' w, p w * g w
  have hterm (v : α) : |g v / E - 1| ≤ b / a - 1 := by
    have h := expect_ratio_mem hp0 hp1 ha hg v
    have hgv : 0 < g v := ha.trans_le (hg v).1
    have hb : 0 < b := ha.trans_le ((hg v).1.trans (hg v).2)
    have hE : 0 < E := by
      have := h.1; rw [le_div_iff₀ hgv] at this; nlinarith [div_pos ha hb]
    have h1 : a / b ≤ g v / E := by
      rw [div_le_div_iff₀ hb hE]
      have := h.2; rw [div_le_div_iff₀ hgv ha] at this; nlinarith
    have h2 : g v / E ≤ b / a := by
      rw [div_le_div_iff₀ hE ha]
      have := h.1; rw [div_le_div_iff₀ hb hgv] at this; nlinarith
    have h3 : 1 - a / b ≤ b / a - 1 := by
      rw [div_sub_one ha.ne', one_sub_div hb.ne', div_le_div_iff₀ hb ha]
      nlinarith [sq_nonneg (a - b)]
    rw [abs_le]; constructor <;> linarith
  calc _ ≤ ∑' v, p v * (b / a - 1) :=
        Summable.tsum_le_tsum (fun v ↦ mul_le_mul_of_nonneg_left (hterm v) (hp0 v))
          (Summable.of_nonneg_of_le (fun v ↦ mul_nonneg (hp0 v) (abs_nonneg _))
            (fun v ↦ mul_le_mul_of_nonneg_left (hterm v) (hp0 v)) (hp1.summable.mul_right _))
          (hp1.summable.mul_right _)
    _ = b / a - 1 := by rw [tsum_mul_right, hp1.tsum_eq, one_mul]

/-- **Part 141 Lemma 2, pointwise ratio.** For any probability `p` on the tail coordinates and any
real centres `w(u) ∈ ℝ^r`, with `g(u) = kleinWeight s q (w u)` and `τ = τ(s/q) < 1`,
`K(h,u)/D_{L,s}(h,u) = E_p[g]/g(u)` lies in `[((1-τ)/(1+τ))^r, ((1+τ)/(1-τ))^r]`. -/
theorem klein_ratio_bounds {α : Type*} {r : ℕ} {s q : ℝ} (hs : 0 < s) (hq : 0 < q)
    (hτ : tau (s / q) < 1) {p : α → ℝ} (hp0 : ∀ u, 0 ≤ p u) (hp1 : HasSum p 1)
    (w : α → Fin r → ℝ) (u : α) :
    ((1 - tau (s / q)) / (1 + tau (s / q))) ^ r ≤
        (∑' v, p v * kleinWeight s q (w v)) / kleinWeight s q (w u) ∧
      (∑' v, p v * kleinWeight s q (w v)) / kleinWeight s q (w u) ≤
        ((1 + tau (s / q)) / (1 - tau (s / q))) ^ r := by
  rw [div_pow, div_pow]
  exact expect_ratio_mem hp0 hp1 (pow_pos (by linarith) r)
    (fun v ↦ kleinWeight_mem hs hq hτ (w v)) u

/-- **Part 141 Lemma 2, statistical distance.**
`SD(K, D_{L,s}) = ½ E_p |g/E_p g - 1| ≤ ½ (((1+τ)/(1-τ))^r - 1)`. -/
theorem klein_sd_le {α : Type*} {r : ℕ} {s q : ℝ} (hs : 0 < s) (hq : 0 < q)
    (hτ : tau (s / q) < 1) {p : α → ℝ} (hp0 : ∀ u, 0 ≤ p u) (hp1 : HasSum p 1)
    (w : α → Fin r → ℝ) :
    (1 / 2) * ∑' v, p v * |kleinWeight s q (w v) / (∑' x, p x * kleinWeight s q (w x)) - 1| ≤
      (1 / 2) * (((1 + tau (s / q)) / (1 - tau (s / q))) ^ r - 1) := by
  rw [div_pow]
  gcongr
  exact expect_abs_sub_le hp0 hp1 (pow_pos (by linarith) r)
    (fun v ↦ kleinWeight_mem hs hq hτ (w v))

/-! ### The recorded instance: `s/q ≥ 38.39` -/

/-- At `s/q ≥ 38.39`, `τ(s/q) < 2^{-6678}`. -/
theorem tau_lt_of_ge {x : ℝ} (hx : 38.39 ≤ x) : tau x < 1 / 2 ^ 6678 := by
  set y := π * x ^ 2 with hy
  have hy0 : 4630 ≤ y := by
    have hx2 : (38.39 : ℝ) ^ 2 ≤ x ^ 2 := by gcongr
    nlinarith [pi_gt_d6, pi_pos]
  have hx0 : 0 < x := by linarith
  have h3 : Real.exp (-3 * y) ≤ 1 / 13891 := by
    have := Real.add_one_le_exp (3 * y)
    rw [show -3 * y = -(3 * y) by ring, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hden : (13890 : ℝ) / 13891 ≤ 1 - Real.exp (-3 * y) := by linarith
  have hlog := log_two_lt_d9
  -- `exp (log 2 - y + 6678 log 2) ≤ exp (-0.47)`
  have hexp : Real.exp (Real.log 2 - y) * Real.exp (6678 * Real.log 2) ≤ Real.exp (-0.46) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; norm_num at hlog ⊢; nlinarith
  have h046 : Real.exp (-0.46) ≤ 1 / 1.46 := by
    have := Real.add_one_le_exp 0.46
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h2pow : (2 : ℝ) ^ 6678 = Real.exp (6678 * Real.log 2) := by
    have := Real.exp_nat_mul (Real.log 2) 6678
    rw [Real.exp_log two_pos] at this
    rw [← this]; norm_num
  calc tau x ≤ 2 * Real.exp (-y) / (1 - Real.exp (-3 * y)) := tau_le hx0
    _ ≤ 2 * Real.exp (-y) / (13890 / 13891) := by
        gcongr
    _ = (13891 / 13890) * Real.exp (Real.log 2 - y) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log two_pos]; ring
    _ < 1 / 2 ^ 6678 := by
        rw [h2pow, lt_div_iff₀ (Real.exp_pos _), mul_assoc]
        have hp := Real.exp_pos (Real.log 2 - y)
        nlinarith

end

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.theta1_poisson
#print axioms SigabaNeo.Wall1.abs_theta1_div_sub_one_le
#print axioms SigabaNeo.Wall1.tau_le
#print axioms SigabaNeo.Wall1.thetaQ_ratio_mem
#print axioms SigabaNeo.Wall1.klein_ratio_bounds
#print axioms SigabaNeo.Wall1.klein_sd_le
#print axioms SigabaNeo.Wall1.tau_lt_of_ge

import Definitions.Def_LatticeAttack_Research_Wall1_InwardCube
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit true

/-! Product interpolation on the integer grid and its radial rounding error. -/
noncomputable section

namespace SigabaNeo.Wall1.RawBallRounding
open Finset Real MeasureTheory
open scoped Classical

private def mass (x : ℝ) (b : Bool) : ℝ :=
  if b then Int.fract x else 1 - Int.fract x

/-- One of the two adjacent integers around a real coordinate. -/
def vertex (x : ℝ) (b : Bool) : ℤ := if b then ⌊x⌋+1 else ⌊x⌋

private lemma vertex_injective (x : ℝ) : Function.Injective (vertex x) := by
  intro a b he
  cases a <;> cases b <;> simp [vertex] at he ⊢ <;> omega

private def err (x : ℝ) (b : Bool) : ℝ := vertex x b - x

private lemma mass_nonneg (x : ℝ) (b : Bool) : 0 ≤ mass x b := by
  cases b <;> simp [mass, Int.fract_nonneg, (Int.fract_lt_one x).le]

private lemma err_sq (x : ℝ) (b : Bool) : (err x b)^2 ≤ 1 := by
  have hl := Int.floor_le x
  have hu := Int.lt_floor_add_one x
  have h : |err x b| ≤ 1 := by
    rw [abs_le]
    cases b <;> simp only [err, vertex, Bool.false_eq_true, ite_false, ite_true, Int.cast_add,
      Int.cast_one] <;> constructor <;> linarith
  simpa only [one_pow, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2

private def weight (x : Fin n → ℝ) (b : Fin n → Bool) := ∏ i, mass (x i) (b i)

private def dotErr (x : Fin n → ℝ) (b : Fin n → Bool) := ∑ i, x i * err (x i) (b i)

private lemma total_mass (x : Fin n → ℝ) : ∑ b, weight x b = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp [mass]

/-- Product probabilities for independent, mean-preserving rounding to adjacent integers. -/
def roundingWeight (x : Fin n → ℝ) (b : Fin n → Bool) : ℝ := weight x b

theorem roundingWeight_nonneg (x : Fin n → ℝ) (b : Fin n → Bool) :
    0 ≤ roundingWeight x b := by
  unfold roundingWeight weight
  exact prod_nonneg fun i _ ↦ mass_nonneg (x i) (b i)

theorem roundingWeight_sum (x : Fin n → ℝ) : ∑ b, roundingWeight x b = 1 :=
  total_mass x

private theorem weighted_energy (x : Fin n → ℝ) (c : ℝ) :
    ∑ b, weight x b * (c + ∑ i, (vertex (x i) (b i) : ℝ)^2) =
      c + (∑ i, (x i)^2) + ∑ i, Int.fract (x i) * (1 - Int.fract (x i)) := by
  induction n generalizing c with
  | zero => simp [weight]
  | succ n ih =>
    let u := x 0
    let y (i : Fin n) := x i.succ
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) ↦ Bool)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, weight, Fin.prod_univ_succ, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    change (∑ b : Bool, ∑ bs : Fin n → Bool, mass u b * weight y bs *
      (c + ((vertex u b : ℝ)^2 + ∑ i, (vertex (y i) (bs i) : ℝ)^2))) = _
    simp_rw [← add_assoc, mul_assoc, ← mul_sum, ih y]
    simp only [Fintype.sum_bool, mass, vertex, Bool.false_eq_true, ite_false, ite_true,
      Int.cast_add, Int.cast_one]
    simp only [u, y, Int.fract]
    ring

/-- Exact expected squared norm: each coordinate contributes its rounding variance. -/
theorem roundingWeight_energy (x : Fin n → ℝ) :
    ∑ b, roundingWeight x b * (∑ i, (vertex (x i) (b i) : ℝ)^2) =
      (∑ i, (x i)^2) + ∑ i, Int.fract (x i) * (1 - Int.fract (x i)) := by
  simpa only [roundingWeight, zero_add] using weighted_energy x 0

/-- Rounding increases expected squared norm by at most one quarter per coordinate. -/
theorem roundingWeight_energy_le (x : Fin n → ℝ) :
    ∑ b, roundingWeight x b * (∑ i, (vertex (x i) (b i) : ℝ)^2) ≤
      (∑ i, (x i)^2) + (n : ℝ)/4 := by
  rw [roundingWeight_energy]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _i : Fin n, (1/4 : ℝ) := sum_le_sum fun i _ ↦ by
      nlinarith [sq_nonneg (Int.fract (x i) - 1/2)]
    _ = _ := by simp; ring

private lemma second_moment (x : Fin n → ℝ) (c : ℝ) :
    ∑ b, weight x b * (c + dotErr x b)^2 =
      c^2 + ∑ i, (x i)^2 * Int.fract (x i) * (1 - Int.fract (x i)) := by
  induction n generalizing c with
  | zero => simp [weight,dotErr]
  | succ n ih =>
    let u := x 0
    let y (i : Fin n) := x i.succ
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) ↦ Bool)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, weight, dotErr, Fin.prod_univ_succ, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    change (∑ b : Bool, ∑ bs : Fin n → Bool, mass u b * weight y bs *
      (c + (u * err u b + dotErr y bs))^2) = _
    simp_rw [← add_assoc, mul_assoc, ← mul_sum, ih y]
    simp only [Fintype.sum_bool, mass, err, vertex, Bool.false_eq_true, ite_false, ite_true,
      Int.cast_add, Int.cast_one]
    simp only [u, y, Int.fract, ← mul_assoc]
    ring

/-- In the inner ball a uniform positive fraction of interpolation mass lands in the outer ball.
The radial error has variance at most one quarter of the squared inner radius. -/
private theorem round_inside {n : ℕ} (hn : n ≤ 558) (x : Fin n → ℝ) {r : ℝ} (hr : 1690 ≤ r)
    (hx : ∑ i, (x i)^2 ≤ (r-7/5)^2) :
    119/144 ≤ ∑ b : Fin n → Bool, if ∑ i, (vertex (x i) (b i):ℝ)^2 ≤ r^2
      then weight x b else 0 := by
  let t := 6/5*r
  have tp : 0 < t := by dsimp [t]; linarith
  have variance := second_moment x 0
  simp only [zero_add, zero_pow (by decide : 2 ≠ 0)] at variance
  have H : ∑ b, weight x b * (dotErr x b)^2 ≤ r^2/4 := by
    rw [variance]
    calc
      _ ≤ ∑ i, (x i)^2 * (1/4) := sum_le_sum fun i _ ↦ by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (Int.fract (x i)-1/2)])
          (sq_nonneg _)
      _ = (∑ i, (x i)^2)/4 := by rw [← sum_mul]; ring
      _ ≤ _ := by nlinarith
  have inside (b : Fin n → Bool) (h : dotErr x b ≤ t) :
      ∑ i, (vertex (x i) (b i):ℝ)^2 ≤ r^2 := by
    have error := sum_le_sum (s := univ) fun (i : Fin n) _ ↦ err_sq (x i) (b i)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at error
    have he : ∑ i, (vertex (x i) (b i):ℝ)^2 =
        (∑ i, (x i)^2) + 2*dotErr x b + ∑ i, (err (x i) (b i))^2 := by
      simp only [dotErr, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun i _ ↦ by dsimp [err]; ring
    rw [he]
    have hn' : (n:ℝ) ≤ 558 := by exact_mod_cast hn
    dsimp [t] at h
    nlinarith
  let good (b : Fin n → Bool) := if ∑ i, (vertex (x i) (b i):ℝ)^2 ≤ r^2 then weight x b else 0
  have bound (b : Fin n → Bool) : (weight x b - good b)*t^2 ≤ weight x b * (dotErr x b)^2 := by
    have wp : 0 ≤ weight x b := prod_nonneg fun i _ ↦ mass_nonneg _ _
    unfold good
    split_ifs with hi
    · simp [mul_nonneg wp (sq_nonneg _)]
    · have h := lt_of_not_ge (mt (inside b) hi)
      rw [sub_zero]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ tp.le h.le _) wp
  have hh := (sum_le_sum (s := univ) fun b _ ↦ bound b).trans H
  rw [← sum_mul, sum_sub_distrib, total_mass] at hh
  change 119/144 ≤ ∑ b, good b
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos tp)).mp
  dsimp [t] at hh ⊢
  nlinarith only [hh]

private def hat (x : ℝ) : ℝ := max 0 (1 - |x|)

private lemma hat_cont : Continuous hat := by unfold hat; fun_prop

private lemma hat_int : Integrable hat := by
  apply hat_cont.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1))
  intro x hx
  unfold hat
  apply max_eq_left
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · linarith [neg_abs_le x]
  · linarith [le_abs_self x]

private lemma hat_integral : ∫ x, hat x = 1 := by
  have hs : Function.support hat ⊆ Set.Ioc (-1) 1 := by
    intro x hx
    change max 0 (1 - |x|) ≠ 0 at hx
    have ht : 0 < 1 - |x| := lt_of_not_ge (fun h ↦ hx (max_eq_left h))
    exact ⟨by linarith [neg_abs_le x],by linarith [le_abs_self x]⟩
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hs,
    ← intervalIntegral.integral_add_adjacent_intervals (hat_cont.intervalIntegrable (μ := volume) (-1) 0)
      (hat_cont.intervalIntegrable (μ := volume) 0 1)]
  have left : (∫ x in (-1:ℝ)..0, hat x) = ∫ x in (-1:ℝ)..0, 1+x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [Set.mem_Icc] at hx
    simp [hat, abs_of_nonpos hx.2, max_eq_right (by linarith : 0 ≤ 1+x)]
  have right : (∫ x in (0:ℝ)..1, hat x) = ∫ x in (0:ℝ)..1, 1-x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [Set.mem_Icc] at hx
    simp [hat,abs_of_nonneg hx.1, max_eq_right (by linarith : 0 ≤ 1-x)]
  rw [left,right,intervalIntegral.integral_add,intervalIntegral.integral_sub] <;>
    norm_num [integral_id]

private def kernel (z : Fin n → ℤ) (x : Fin n → ℝ) := ∏ i, hat (x i - z i)

private theorem kernel_int (z : Fin n → ℤ) : Integrable (kernel z) :=
  Integrable.fintype_prod fun i ↦ hat_int.comp_sub_right (z i : ℝ)

private theorem kernel_integral (z : Fin n → ℤ) : ∫ x, kernel z x = 1 := by
  unfold kernel
  rw [integral_fintype_prod_volume_eq_prod (fun i (x : ℝ) ↦ hat (x - z i))]
  simp only [integral_sub_right_eq_self, hat_integral, prod_const_one]

private lemma hat_vertex (x : ℝ) (b : Bool) : mass x b = hat (x - vertex x b) := by
  have hl := Int.floor_le x
  have hu := Int.lt_floor_add_one x
  cases b
  · simp only [mass, vertex, Bool.false_eq_true, ite_false, hat, Int.fract,
      abs_of_nonneg (by linarith : 0 ≤ x - ⌊x⌋), max_eq_right (by linarith : 0 ≤ 1-(x-⌊x⌋))]
  · simp only [mass, vertex, ite_true, hat, Int.cast_add, Int.cast_one, Int.fract,
      abs_of_nonpos (by linarith : x-(⌊x⌋+1) ≤ 0)]
    rw [max_eq_right (by linarith)]
    ring

/-- The product tent kernel centered at an integer point. -/
def tentKernel (z : Fin n → ℤ) (x : Fin n → ℝ) : ℝ := kernel z x

theorem tentKernel_nonneg (z : Fin n → ℤ) (x : Fin n → ℝ) : 0 ≤ tentKernel z x := by
  unfold tentKernel kernel hat
  exact prod_nonneg fun i _ ↦ le_max_left _ _

theorem tentKernel_integrable (z : Fin n → ℤ) : Integrable (tentKernel z) := kernel_int z

theorem tentKernel_integral (z : Fin n → ℤ) : ∫ x, tentKernel z x = 1 :=
  kernel_integral z

/-- Adjacent-integer rounding probabilities are values of the same tent kernel. -/
theorem roundingWeight_eq_tentKernel (x : Fin n → ℝ) (b : Fin n → Bool) :
    roundingWeight x b = tentKernel (fun i ↦ vertex (x i) (b i)) x := by
  unfold roundingWeight weight tentKernel kernel
  exact prod_congr rfl fun i _ ↦ hat_vertex _ _

theorem roundingVertex_injective (x : Fin n → ℝ) :
    Function.Injective (fun b : Fin n → Bool ↦ fun i ↦ vertex (x i) (b i)) := by
  intro a b he
  funext i
  exact vertex_injective (x i) (congrFun he i)

/-- Any finite family of prefix tent kernels has integrated mass equal to its cardinality.
The prefix map need not be injective; repeated prefixes are counted with multiplicity. -/
theorem tentKernel_integral_bound {α : Type*} (S : Finset α) (proj : α → Fin n → ℤ)
    (D : Set (Fin n → ℝ)) (hD : MeasurableSet D) (F : (Fin n → ℝ) → ℝ)
    (hF : IntegrableOn F D)
    (hbound : ∀ x ∈ D, F x ≤ ∑ z ∈ S, tentKernel (proj z) x) :
    (∫ x in D, F x) ≤ (S.card : ℝ) := by
  have hi : Integrable (fun x ↦ ∑ z ∈ S, tentKernel (proj z) x) :=
    integrable_finsetSum _ fun z _ ↦ tentKernel_integrable (proj z)
  have hmono := setIntegral_mono_on hF hi.integrableOn hD hbound
  apply hmono.trans
  calc
    _ ≤ ∫ x, ∑ z ∈ S, tentKernel (proj z) x :=
      setIntegral_le_integral hi (ae_of_all _ fun x ↦
        sum_nonneg fun z _ ↦ tentKernel_nonneg (proj z) x)
    _ = _ := by
      rw [integral_finsetSum _ (fun z _ ↦ tentKernel_integrable (proj z))]
      simp [tentKernel_integral]

/-- Each admissible real input has a substantial rounding mass in the integer set.
Each integer receives total integrated mass one. -/
theorem interpolation_count {n : ℕ} (hn : n ≤ 558) {r : ℝ} (hr : 1690 ≤ r)
    (D : Set (Fin n → ℝ)) (hD : MeasurableSet D) (hf : volume D ≠ ⊤)
    (S : Finset (Fin n → ℤ)) (inner : ∀ x ∈ D, ∑ i, (x i)^2 ≤ (r-7/5)^2)
    (cover : ∀ x ∈ D, ∀ b : Fin n → Bool, ∑ i, (vertex (x i) (b i):ℝ)^2 ≤ r^2 →
      (fun i ↦ vertex (x i) (b i)) ∈ S) :
    volume.real D * (119/144) ≤ S.card := by
  have pt (x : Fin n → ℝ) (hx : x ∈ D) : 119/144 ≤ ∑ z ∈ S, kernel z x := by
    let f (b : Fin n → Bool) (i : Fin n) := vertex (x i) (b i)
    let T := univ.filter fun b : Fin n → Bool ↦ ∑ i, (f b i:ℝ)^2 ≤ r^2
    have inj : Function.Injective f := by
      intro a b he
      funext i
      have h := congrFun he i
      change vertex (x i) (a i) = vertex (x i) (b i) at h
      exact vertex_injective _ h
    have sub : T.image f ⊆ S := by
      rintro _ he
      obtain ⟨b,hb,rfl⟩ := mem_image.mp he
      exact cover x hx b (mem_filter.mp hb).2
    apply (round_inside hn x hr (inner x hx)).trans
    rw [← sum_filter]
    change ∑ b ∈ T, weight x b ≤ _
    have eqn (b) : weight x b = kernel (f b) x := prod_congr rfl fun i _ ↦ hat_vertex _ _
    simp_rw [eqn]
    rw [← sum_image (s := T) (f := fun z ↦ kernel z x) inj.injOn]
    exact sum_le_sum_of_subset_of_nonneg sub fun z _ _ ↦ prod_nonneg fun i _ ↦ le_max_left _ _
  have hi : Integrable (fun x ↦ ∑ z ∈ S, kernel z x) := integrable_finsetSum _ fun z _ ↦ kernel_int z
  have hmono := setIntegral_mono_on (μ := volume) (f := fun _ ↦ (119/144 : ℝ))
    (g := fun x ↦ ∑ z ∈ S, kernel z x) (integrableOn_const hf) hi.integrableOn hD pt
  rw [setIntegral_const, smul_eq_mul] at hmono
  apply hmono.trans
  calc
    _ ≤ ∫ x, ∑ z ∈ S, kernel z x := setIntegral_le_integral hi (ae_of_all _ fun x ↦
      sum_nonneg fun z _ ↦ prod_nonneg fun i _ ↦ le_max_left _ _)
    _ = _ := by rw [integral_finsetSum _ (fun z _ ↦ kernel_int z)]; simp [kernel_integral]

end SigabaNeo.Wall1.RawBallRounding

#print axioms SigabaNeo.Wall1.RawBallRounding.roundingWeight_nonneg
#print axioms SigabaNeo.Wall1.RawBallRounding.roundingWeight_sum
#print axioms SigabaNeo.Wall1.RawBallRounding.roundingWeight_energy
#print axioms SigabaNeo.Wall1.RawBallRounding.roundingWeight_energy_le
#print axioms SigabaNeo.Wall1.RawBallRounding.interpolation_count
#print axioms SigabaNeo.Wall1.RawBallRounding.tentKernel_nonneg
#print axioms SigabaNeo.Wall1.RawBallRounding.tentKernel_integrable
#print axioms SigabaNeo.Wall1.RawBallRounding.tentKernel_integral
#print axioms SigabaNeo.Wall1.RawBallRounding.roundingWeight_eq_tentKernel
#print axioms SigabaNeo.Wall1.RawBallRounding.roundingVertex_injective
#print axioms SigabaNeo.Wall1.RawBallRounding.tentKernel_integral_bound

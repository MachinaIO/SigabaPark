import Definitions.Def_LatticeAttack_Research_Wall1_ControlledPlanePairs
import Definitions.Def_LatticeAttack_Research_Wall1_DualMinimumExitNumeric

set_option autoImplicit true

/-! Radius-250 raw exit and the entirely old term of the draw-154 flag test. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open QaryMembership DualExit DualExit.Certificate Finset MeasureTheory Metric
open scoped Classical Matrix
variable {m n q : ℕ} [Fact q.Prime]

def rawMember (A : Design m n q) (z : Grid m n) : Prop :=
  A *ᵥ (fun j ↦ (z (.inr j) : ZMod q)) = fun i ↦ (z (.inl i) : ZMod q)

def rawShort (A : Design m n q) (r : ℝ) : Prop :=
  ∃ z : Grid m n, z ≠ 0 ∧ sqLength z ≤ r^2 ∧ rawMember A z

/-- Below the modulus any eligible nonzero short vector imposes one constraint per
row. The inward-volume factor of two here even permits counting both signs. -/
theorem rawShort_bound {r : ℝ} (hr : 0 ≤ r) (hq : r < q) :
    probability (fun A : Design m n q ↦ rawShort A r) ≤
      2 * inwardVolume (Coord m n) r / (q : ℝ)^m := by
  let S := SigabaNeo.Planted.integerBall (ι := Coord m n) r
  have cover (A : Design m n q) (h : rawShort A r) : ∃ z ∈ S, rawMember A z := by
    obtain ⟨z,hn,hs,hm⟩ := h
    exact ⟨z,(SigabaNeo.Planted.mem_integerBall hr z).mpr ⟨hn,hs⟩,hm⟩
  have fixed (z : Grid m n) (hz : z ∈ S) :
      probability (fun A : Design m n q ↦ rawMember A z) ≤ 1 / (q : ℝ)^m := by
    let w : Point m n := (fun i ↦ -z (.inl i), fun j ↦ z (.inr j))
    have eqn (A : Design m n q) : rawMember A z ↔ kernel A w := by
      have ht : -reduce q w.1 = fun i ↦ (z (.inl i) : ZMod q) := by
        funext i
        change -((-z (.inl i) : ℤ) : ZMod q) = (z (.inl i) : ZMod q)
        simp
      rw [rawMember, kernel, ht]
      rfl
    obtain ⟨hn,hs⟩ := (SigabaNeo.Planted.mem_integerBall hr z).mp hz
    by_cases he : reduce q w.2 = 0
    · have impossible (A : Design m n q) : ¬rawMember A z := by
        intro ha
        have hout : reduce q w.1 = 0 := by
          have h := (eqn A).mp ha
          simpa [kernel, he, eq_comm] using h
        apply hn
        funext i
        have hz0 : ((z i : ℤ) : ZMod q) = 0 := by
          cases i with
          | inl i => simpa [w,reduce] using congrFun hout i
          | inr j => exact congrFun he j
        have hsq := (single_le_sum (fun i (_ : i ∈ univ) ↦ sq_nonneg (z i : ℝ))
          (mem_univ i)).trans hs
        have hab : |(z i : ℝ)| < q := (abs_le_of_sq_le_sq hsq hr).trans_lt hq
        have hi : |z i| < (q : ℤ) := by exact_mod_cast hab
        by_contra hne
        exact hi.not_ge (Int.le_of_dvd (abs_pos.mpr hne)
          ((dvd_abs _ _).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp hz0)))
      simp [probability, designs, impossible]
    · have hc := kernel_fixed w he
      rw [card_univ] at hc
      simp_rw [eqn]
      unfold probability
      apply le_of_eq
      apply (div_eq_div_iff (by exact_mod_cast (Fintype.card_pos (α := Design m n q)).ne')
        (pow_ne_zero _ (by exact_mod_cast (Fact.out : q.Prime).ne_zero))).mpr
      simpa only [one_mul] using (show ((designs (fun A : Design m n q ↦ kernel A w)).card : ℝ) *
        (q:ℝ)^m = Fintype.card (Design m n q) by exact_mod_cast hc)
  have hu := (probability_mono cover).trans
    (probability_exists_le S fun z (A : Design m n q) ↦ rawMember A z)
  have hv := inward_half_cube S r (fun z hz ↦ ((SigabaNeo.Planted.mem_integerBall hr z).mp hz).2)
  calc
    _ ≤ ∑ z ∈ S, 1 / (q : ℝ)^m := hu.trans (sum_le_sum fixed)
    _ = (S.card : ℝ) / (q : ℝ)^m := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hv]) (by positivity)

local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private theorem raw_numeric {n d k : ℕ} {r : ℝ} {b c p s : ℕ}
    (hd : Fintype.card (Coord 400 n) = d) (hk : d = 2*k+1) (hr : 0 ≤ r) (hq : r < 3329)
    (hc : 0 < c) (hs : 0 < s) (hb : r^2 + d/4 ≤ ((b:ℝ)/c)^2)
    (cert : 2*b^d*22^k*2^(k+1)*s < p*c^d*7^k*d.doubleFactorial*3329^400) :
    probability (fun A : Design 400 n 3329 ↦ rawShort A r) < (p : ℝ)/s := by
  have dim : Module.finrank ℝ (Space 400 n) = d := by simpa using hd
  have hV := InnerProductSpace.volume_ball_of_dim_odd (dim.trans hk) (0 : Space 400 n) 1
  have vol : volume.real (ball (0 : Space 400 n) 1) =
      Real.pi^k * 2^(k+1) / d.doubleFactorial := by
    rw [Measure.real, hV, dim, ENNReal.ofReal_one, one_pow, one_mul,
      ENNReal.toReal_ofReal (by positivity)]
  have hR := (Real.sqrt_le_left (show 0 ≤ (b:ℝ)/c by positivity)).mpr hb
  have hpi : Real.pi ≤ 22/7 := by linarith [Real.pi_lt_d4]
  have hD : (0:ℝ) < d.doubleFactorial := by positivity
  have hcert : 2*(b:ℝ)^d*22^k*2^(k+1)*s <
      p*(c:ℝ)^d*7^k*(d.doubleFactorial:ℝ)*3329^400 := by exact_mod_cast cert
  apply (rawShort_bound hr (by exact_mod_cast hq)).trans_lt
  unfold inwardVolume
  rw [hd, vol]
  have hv := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ Real.pi_pos.le hpi k) (show 0 ≤ (2:ℝ)^(k+1) by positivity)) hD.le
  apply lt_of_le_of_lt (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul (pow_le_pow_left₀ (Real.sqrt_nonneg _) hR _) hv
      (by positivity) (by positivity)) (by norm_num : (0:ℝ) ≤ 2)) (by positivity)) _
  simp only [div_pow]
  have hc' : 0 < (c:ℝ) := by exact_mod_cast hc
  have hs' : 0 < (s:ℝ) := by exact_mod_cast hs
  field_simp
  simpa only [Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using hcert

set_option maxRecDepth 10000 in
theorem raw250_numeric :
    probability (fun A : Design 400 511 3329 ↦ rawShort A 250) < 4249 / (10:ℝ)^15 := by
  simp only [← Nat.cast_ofNat (R := ℝ) (n := 10), ← Nat.cast_pow]
  apply raw_numeric (r := 250) (k := 455) (d := 911) (b := 501) (c := 2) (p := 4249) (s := 10^15)
    (by simp [Coord]) (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)
  decide +kernel

set_option maxRecDepth 10000 in
theorem initial2885_numeric :
    probability (fun A : Design 400 105 3329 ↦ rawShort A 2885) < 1 / (10:ℝ)^34 := by
  simp only [← Nat.cast_ofNat (R := ℝ) (n := 10), ← Nat.cast_pow]
  rw [← Nat.cast_one (R := ℝ)]
  apply raw_numeric (r := 2885) (k := 252) (d := 505) (b := 2886) (c := 1) (p := 1) (s := 10^34)
    (by simp [Coord]) (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)
  decide +kernel

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.rawShort_bound
#print axioms SigabaNeo.Wall1.ControlledPlane.raw250_numeric
#print axioms SigabaNeo.Wall1.ControlledPlane.initial2885_numeric

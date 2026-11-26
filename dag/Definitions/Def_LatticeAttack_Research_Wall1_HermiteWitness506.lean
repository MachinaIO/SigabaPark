import Definitions.Def_LatticeAttack_Research_Wall1_TerminalScale506
import Definitions.Def_LatticeAttack_Reduction_Hermite2

set_option autoImplicit true

/-! # The rational spherical polynomial witness for the rank-506 Hermite cap

The coefficient recurrence is the normalized Gegenbauer recurrence at the rational threshold
in the Hermite-cap note. We check the coefficients of both factors, the constant term from
spherical orthogonality, and the volume conversion at an inward-rounded squared radius.
-/

namespace SigabaNeo.Wall1.HermiteWitness506

def threshold : ℚ := 4125869 / 10000000

/-- The pair of Gegenbauer values at degrees j and j+1. -/
def gegenbauerPair : ℕ → ℚ × ℚ
  | 0 => (1, threshold)
  | j+1 =>
    let (a, b) := gegenbauerPair j
    let k : ℚ := j + 1
    (b, ((2*k+504)*threshold*b-k*a)/(k+504))

/-- Dimension of degree-j spherical harmonics, in factorial form. -/
def multiplicity (j : ℕ) : ℚ :=
  ((2*j+504 : ℕ) : ℚ) * (j+503).descFactorial j / (504 * (j.factorial : ℚ))

/-- Coefficients of q in the normalized spherical basis, extended by zero. -/
def q (j : ℕ) : ℚ :=
  if j < 32 then multiplicity j * (1 - (gegenbauerPair j).1 / (gegenbauerPair 32).1) else 0

/-- Coefficients of (x-t)q from tridiagonal multiplication by x. -/
def v (j : ℕ) : ℚ :=
  (if j = 0 then 0 else q (j-1) * ((j:ℚ)+503) / (2*j+502)) +
    q (j+1) * ((j:ℚ)+1) / (2*j+506) - threshold * q j

def fZero : ℚ := ∑ j ∈ Finset.range 32, q j * v j / multiplicity j

def lpRatio : ℚ := (∑ j ∈ Finset.range 32, q j) * (∑ j ∈ Finset.range 33, v j) / fZero

/-- A rational squared radius below the verified enlargement in the paper certificate. -/
def radiusSq : ℚ := 85279943022 / 100000000000

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem coefficient_signs : ∀ j : Fin 33, 0 ≤ q j ∧ 0 ≤ v j := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem constant_term_pos : 0 < fZero := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem ratio_enclosure : lpRatio ≤ 190710711816152 * 10^37 := by decide +kernel

open TerminalProjection

/-- Exact rational enclosure after converting the count bound to Hermite units. -/
theorem volume_conversion :
    (lpRatio : ℝ) ≤ terminalBallVolume * (radiusSq : ℝ)^253 * (56.2142 : ℝ)^253 := by
  have hn : (190710711816152 * 10^37 : ℚ) * (Nat.factorial 253 : ℚ) ≤
      (3.14159265358979323846 * radiusSq * 56.2142)^253 := by decide +kernel
  have hp : (3.14159265358979323846 : ℝ) ≤ Real.pi := Real.pi_gt_d20.le
  have hr : 0 ≤ (radiusSq : ℝ) := by norm_num [radiusSq]
  rw [terminalBallVolume_eq]
  have h₁ := (Rat.cast_le (K := ℝ)).mpr ratio_enclosure
  have h₂ := (Rat.cast_le (K := ℝ)).mpr hn
  push_cast at h₁ h₂
  calc
    _ ≤ 190710711816152 * 10^37 := h₁
    _ ≤ (3.14159265358979323846 * (radiusSq : ℝ) * 56.2142)^253 /
        (Nat.factorial 253 : ℝ) := (le_div_iff₀ (by positivity)).mpr h₂
    _ ≤ (Real.pi * (radiusSq : ℝ) * 56.2142)^253 / (Nat.factorial 253 : ℝ) := by gcongr
    _ = _ := by ring


/-- The actual Blichfeldt coefficient in this dimension has a disjoint rational enclosure. -/
theorem blichfeldt_enclosure :
    61.45237 < BKZ.blichfeldtConstant 506 ∧ BKZ.blichfeldtConstant 506 < 61.45238 := by
  let r := (Nat.factorial 254 : ℝ)^((253 : ℝ)⁻¹)
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hpow : r^253 = (Nat.factorial 254 : ℝ) :=
    Real.rpow_inv_natCast_pow (by positivity) (by decide)
  have hcoef : BKZ.blichfeldtConstant 506 = (2*r)/Real.pi := by
    unfold BKZ.blichfeldtConstant r
    rw [show ((506 : ℕ) : ℝ)/2+2 = (254:ℕ)+1 by norm_num, Real.Gamma_nat_eq_factorial]
    rw [show (2:ℝ)/((506:ℕ):ℝ) = (253:ℝ)⁻¹ by norm_num]
    change 2/Real.pi * r = 2*r/Real.pi
    rw [div_mul_eq_mul_div]
  have hlo : (61.45237 * 3.14159265358979323847 / 2 : ℝ)^253 < Nat.factorial 254 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (show (61.45237 * 3.14159265358979323847 / 2 : ℚ)^253 < Nat.factorial 254
      by decide +kernel)
    push_cast at h
    exact h
  have hhi : (Nat.factorial 254 : ℝ) < (61.45238 * 3.14159265358979323846 / 2)^253 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (show (Nat.factorial 254 : ℚ) < (61.45238 * 3.14159265358979323846 / 2)^253
      by decide +kernel)
    push_cast at h
    exact h
  have hl := lt_of_pow_lt_pow_left₀ 253 hr (hlo.trans_eq hpow.symm)
  have hh := lt_of_pow_lt_pow_left₀ 253 (by positivity) (hpow.trans_lt hhi)
  clear_value r
  rw [hcoef]
  constructor
  · apply (lt_div_iff₀ Real.pi_pos).mpr
    calc
      (61.45237:ℝ) * Real.pi ≤ 61.45237 * 3.14159265358979323847 :=
        mul_le_mul_of_nonneg_left Real.pi_lt_d20.le (by norm_num)
      _ < 2*r := by linarith only [hl]
  · apply (div_lt_iff₀ Real.pi_pos).mpr
    calc
      2*r < 61.45238 * 3.14159265358979323846 := by linarith only [hh]
      _ ≤ 61.45238 * Real.pi := mul_le_mul_of_nonneg_left Real.pi_gt_d20.le (by norm_num)

/-- The unconditional shortest-vector cap supplied by Blichfeldt alone. -/
theorem blichfeldt_shortest (L : Submodule ℤ (EuclideanSpace ℝ (Fin 506)))
    [DiscreteTopology L] [IsZLattice ℝ L] {x : EuclideanSpace ℝ (Fin 506)}
    (hx : DecoupledDecoder.IsShortest L x) :
    ‖x‖^2 < 61.45238 * ZLattice.covolume L ^ (2/(506:ℝ)) := by
  obtain ⟨v, hv, h⟩ := BKZ.hermite_blichfeldt L
  have hxv := hx.2.2 v.val v.property (fun e ↦ hv (Subtype.ext e))
  refine ((pow_le_pow_left₀ (norm_nonneg _) hxv 2).trans h).trans_lt ?_
  exact mul_lt_mul_of_pos_right blichfeldt_enclosure.2
    (Real.rpow_pos_of_pos (ZLattice.covolume_pos L MeasureTheory.volume) _)

open MeasureTheory Metric in
/-- Integrating the number of points in a translated ball over a fundamental domain gives
the ball volume, before normalizing by covolume. This holds even for open balls and radius zero. -/
theorem translated_ball_first_moment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (A : Set E)
    (hA : IsAddFundamentalDomain L.toAddSubgroup A volume) (r : ℝ) :
    (∫⁻ x in A, ∑' v : L.toAddSubgroup, (ball (0:E) r).indicator (1 : E → ENNReal)
      (v.val + x)) = volume (ball (0:E) r) := by
  let : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  have hm : Measurable ((ball (0:E) r).indicator (1 : E → ENNReal)) :=
    measurable_const.indicator measurableSet_ball
  rw [lintegral_tsum (f := fun (v : L.toAddSubgroup) (x : E) ↦
    (ball (0:E) r).indicator (1 : E → ENNReal) (v.val+x))
    (fun v ↦ (hm.comp (measurable_const.add measurable_id)).aemeasurable)]
  exact (hA.lintegral_eq_tsum'' _).symm.trans (lintegral_indicator_one measurableSet_ball)

open MeasureTheory in
/-- Convert the translated-ball first moment and the integrated spherical pair bound
into the precise physical cap. N is the number of points in the averaging ball. -/
theorem shortest_cap_of_ball_moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (N : Ω → ℝ) (hN : Integrable N μ)
    (hN₂ : Integrable (fun x ↦ N x ^ 2) μ) {s D : ℝ} (hs : 0 < s) (hD : 0 < D)
    (hmean : ∫ x, N x ∂μ = terminalBallVolume * (radiusSq : ℝ)^253 * (s^2)^253 / D)
    (hpair : (fZero : ℝ) * (∫ x, N x ^ 2 ∂μ) ≤
      ((∑ j ∈ Finset.range 32, q j) * (∑ j ∈ Finset.range 33, v j) : ℚ) *
        (∫ x, N x ∂μ)) :
    s^2 ≤ 56.2142 * D^(2/(506 : ℝ)) := by
  let m := ∫ x, N x ∂μ
  have hvol : 0 < terminalBallVolume := by rw [terminalBallVolume_eq]; positivity
  have hr : 0 < (radiusSq : ℝ) := by norm_num [radiusSq]
  have hm : 0 < m := by dsimp [m]; rw [hmean]; positivity
  have hvar : m^2 ≤ ∫ x, N x^2 ∂μ := by
    have hn : 0 ≤ ∫ x, (N x ^ 2 - (2*m)*N x) + m^2 ∂μ :=
      integral_nonneg fun x ↦ by
        change 0 ≤ N x ^ 2 - (2*m)*N x + m^2
        nlinarith [sq_nonneg (N x - m)]
    have hsub : Integrable (fun x ↦ N x^2 - (2*m)*N x) μ := hN₂.sub (hN.const_mul _)
    rw [integral_add hsub (integrable_const (m^2)),
      integral_sub hN₂ (hN.const_mul (2*m)), integral_const_mul, integral_const] at hn
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hn
    change 0 ≤ (∫ x, N x^2 ∂μ) - (2*m)*m + m^2 at hn
    linarith
  have hf : 0 < (fZero : ℝ) := by exact_mod_cast constant_term_pos
  have hmle : m ≤ (lpRatio : ℝ) := by
    unfold lpRatio
    rw [Rat.cast_div]
    apply (le_div_iff₀ hf).mpr
    apply le_of_mul_le_mul_right _ hm
    calc
      _ = (fZero : ℝ)*m^2 := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hvar hf.le).trans hpair
  have h := hmle.trans volume_conversion
  change (∫ x, N x ∂μ) ≤ _ at h
  rw [hmean, div_le_iff₀ hD, mul_assoc (terminalBallVolume * _) _ D] at h
  have hout := le_of_mul_le_mul_left h (mul_pos hvol (pow_pos hr 253))
  apply le_of_pow_le_pow_left₀ (by decide : 253 ≠ 0) (by positivity)
  rw [mul_pow, show 2/(506:ℝ) = (253:ℝ)⁻¹ by norm_num,
    show (D ^ (253:ℝ)⁻¹)^253 = D from Real.rpow_inv_natCast_pow (n := 253) hD.le (by decide)]
  exact hout

end SigabaNeo.Wall1.HermiteWitness506

#print axioms SigabaNeo.Wall1.HermiteWitness506.coefficient_signs
#print axioms SigabaNeo.Wall1.HermiteWitness506.constant_term_pos
#print axioms SigabaNeo.Wall1.HermiteWitness506.ratio_enclosure
#print axioms SigabaNeo.Wall1.HermiteWitness506.volume_conversion

#print axioms SigabaNeo.Wall1.HermiteWitness506.blichfeldt_enclosure
#print axioms SigabaNeo.Wall1.HermiteWitness506.blichfeldt_shortest
#print axioms SigabaNeo.Wall1.HermiteWitness506.translated_ball_first_moment
#print axioms SigabaNeo.Wall1.HermiteWitness506.shortest_cap_of_ball_moments

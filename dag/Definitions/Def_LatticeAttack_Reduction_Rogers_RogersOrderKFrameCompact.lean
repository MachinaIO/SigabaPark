import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKFrame
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKMoment

set_option autoImplicit true

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace SigabaNeo.Rogers.Frame

private def ballTest (n k j : ℕ) (x : Fin k → E n) :=
  ∏ i, densityTest n j (x i)

private theorem tsum_prod_tuple {V : Type*} (u : V → ℝ≥0∞) (k : ℕ) :
    (∑' z : Fin k → V, ∏ i, u (z i)) = (∑' v, u v)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← ih, ← ENNReal.tsum_mul_right]
    rw [← (Fin.consEquiv (fun _ : Fin (k+1) ↦ V)).tsum_eq (fun z ↦ ∏ i, u (z i))]
    simp only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    rw [tsum_prod (f := fun (v : V) (z : Fin k → V) ↦ u v * ∏ i, u (z i))]
    apply tsum_congr
    intro v
    rw [← ENNReal.tsum_mul_left]

private theorem ballTest_work (n k j : ℕ) (g : SL n) :
    tupleWorkload (ballTest n k j) (QuotientGroup.mk g) = (densityWork n j g)^k := by
  let V := {x : E n // x ∈ points (QuotientGroup.mk g) ∧ x ≠ 0}
  let u := fun x : V ↦ densityTest n j x.val
  have h : densityWork n j g = ∑' v : V, u v :=
    (Equiv.funUnique (Fin 1) V).tsum_eq u
  rw [h]
  exact tsum_prod_tuple u k

theorem frameMeasure_finiteOnCompacts {n k : ℕ} (hk : 0 < k) (hn : k < n) {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤) :
    IsFiniteMeasureOnCompacts (frameMeasure (k := k) D) := by
  constructor
  intro K hK
  obtain ⟨r,hr⟩ := hK.isBounded.subset_ball 0
  obtain ⟨R,hR⟩ := exists_nat_gt r
  have ev := (densityWork_power_limit k hk hn hd hfin).eventually (gt_mem_nhds hfin.lt_top)
  obtain ⟨j,hj,hj'⟩ := (ev.and (eventually_ge_atTop R)).exists
  let B := densityBall n j
  have sub : ∀ x ∈ K, ∀ i, x i ∈ B := by
    intro x hx i
    have hh := hr hx
    rw [Metric.mem_ball, dist_zero_right] at hh
    change dist (x i) 0 < (j : ℝ) + 1
    rw [dist_zero_right]
    have := norm_le_pi_norm x i
    have : (R : ℝ) ≤ j := by exact_mod_cast hj'
    linarith
  have m : Measurable (ballTest n k j) :=
    Finset.measurable_prod _ fun i _ ↦ (densityTest_measurable n j).comp (measurable_pi_apply i)
  have htotal := domain_lintegral_tupleWorkload (groupHaar n) D m
  simp_rw [ballTest_work] at htotal
  have sumBound : (∫⁻ x, ballTest n k j x ∂frameMeasure (k := k) D) ≤
      ∫⁻ g in D, (densityWork n j g)^k ∂groupHaar n := by
    rw [frameMeasure_lintegral D _ m, htotal]
    exact (CompleteLattice.summable.tsum_add_tsum_compl (s := independent n k)
      (f := fun z : IntegerTuple n k ↦ ∫⁻ g in D, ballTest n k j (fun i ↦ WithLp.toLp 2 (g • fun l ↦ ((z i).val l : ℝ))) ∂groupHaar n) CompleteLattice.summable) ▸ le_self_add
  have hv : volume B ≠ 0 :=
    (Metric.measure_ball_pos volume _ (by positivity : 0 < (j : ℝ) + 1)).ne'
  have hv' : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have le (x) : K.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ (volume B)^k * ballTest n k j x := by
    by_cases hx : x ∈ K
    · simp [hx, ballTest, densityTest, show ∀ i, x i ∈ densityBall n j from sub x hx, ← mul_pow, B, ENNReal.mul_inv_cancel hv hv']
    · simp [hx]
  have h := lintegral_mono (μ := frameMeasure (k := k) D) le
  rw [lintegral_indicator hK.measurableSet, setLIntegral_const, one_mul,
    lintegral_const_mul' _ _ (ENNReal.pow_ne_top hv')] at h
  exact lt_of_le_of_lt h (ENNReal.mul_ne_top (ENNReal.pow_ne_top hv') (sumBound.trans_lt hj).ne).lt_top

end SigabaNeo.Rogers.Frame

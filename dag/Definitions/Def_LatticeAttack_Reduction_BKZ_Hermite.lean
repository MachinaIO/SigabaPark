module

public import Mathlib

set_option autoImplicit true

/-! # Minkowski's cube bound

For full lattices in real coordinate space the squared Euclidean length of some nonzero
vector is at most k times the squared covolume root. Uses Minkowski's convex body theorem
with a closed cube. The Euclidean ball and a half-integer Gamma bound give the coefficient
(k+4)/π for squared lengths.
-/

open MeasureTheory Metric Module ZSpan
public section

namespace SigabaNeo.BKZ

theorem hermite_cube {k : ℕ} [NeZero k] (L : Submodule ℤ (Fin k → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v : L, v ≠ 0 ∧ ∑ i, (v.val i)^2 ≤
      k * (ZLattice.covolume L ^ (1/(k:ℝ)))^2 := by
  let D := ZLattice.covolume L
  let R := D ^ (1/(k:ℝ))
  have hp : 0 < D := ZLattice.covolume_pos L volume
  have hk : (k:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne k
  have hr : 0 ≤ R := Real.rpow_nonneg hp.le _
  have hrk : R^k = D := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    simp [hk]
  let b := Free.chooseBasis ℤ L
  have fund := ZLattice.isAddFundamentalDomain b volume
  have vol : volume (fundamentalDomain (b.ofZLatticeBasis ℝ)) = ENNReal.ofReal D := by
    rw [show D = _ from ZLattice.covolume_eq_measure_fundamentalDomain L volume fund]
    exact (ENNReal.ofReal_toReal (fundamentalDomain_isBounded _).measure_lt_top.ne).symm
  have dim : Module.finrank ℝ (Fin k → ℝ) = k := by simp
  have size : volume (fundamentalDomain (b.ofZLatticeBasis ℝ)) * 2 ^ Module.finrank ℝ (Fin k → ℝ) ≤
      volume (closedBall (0 : Fin k → ℝ) R) := by
    rw [vol, dim, Real.volume_pi_closedBall _ hr, Fintype.card_fin, mul_pow, hrk,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp [mul_comm]
  let : Countable L.toAddSubgroup := (inferInstance : Countable L)
  let : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  obtain ⟨v,hv,hm⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := L.toAddSubgroup) fund (fun x hx ↦ by simpa using hx)
    (convex_closedBall _ _) (isCompact_closedBall _ _) size
  refine ⟨v,hv,?_⟩
  have bound : ‖(v.val : Fin k → ℝ)‖ ≤ R := by simpa using hm
  calc
    _ ≤ ∑ _ : Fin k, R^2 := Finset.sum_le_sum fun i _ ↦ by
      have hi := (norm_le_pi_norm v.val i).trans bound
      simpa [Real.norm_eq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).mpr hi
    _ = _ := by simp [R,D]

/-- The Minkowski ball radius in dimension k, expressed using the exact unit ball volume. -/
theorem hermite_ball {k : ℕ} [NeZero k] (L : Submodule ℤ (EuclideanSpace ℝ (Fin k)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v : L, v ≠ 0 ∧ ‖v.val‖ ≤ 2 * (ZLattice.covolume L /
      (Real.sqrt Real.pi ^ k / Real.Gamma ((k:ℝ)/2 + 1))) ^ (1/(k:ℝ)) := by
  let U := Real.sqrt Real.pi ^ k / Real.Gamma ((k:ℝ)/2 + 1)
  let D := ZLattice.covolume L
  let R := (D/U) ^ (1/(k:ℝ))
  have hU : 0 < U := div_pos (pow_pos (Real.sqrt_pos.2 Real.pi_pos) _)
    (Real.Gamma_pos_of_pos (by positivity))
  have hD : 0 < D := ZLattice.covolume_pos L volume
  have hk : (k:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne k
  have hR : 0 < R := Real.rpow_pos_of_pos (div_pos hD hU) _
  have powR : R^k = D/U := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hD hU).le]
    simp [hk]
  let b := Free.chooseBasis ℤ L
  have fund := ZLattice.isAddFundamentalDomain b volume
  have vol : volume (fundamentalDomain (b.ofZLatticeBasis ℝ)) = ENNReal.ofReal D := by
    rw [show D = _ from ZLattice.covolume_eq_measure_fundamentalDomain L volume fund]
    exact (ENNReal.ofReal_toReal (fundamentalDomain_isBounded _).measure_lt_top.ne).symm
  have size : volume (fundamentalDomain (b.ofZLatticeBasis ℝ)) *
      2 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) ≤
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) (2*R)) := by
    rw [vol, EuclideanSpace.volume_closedBall, finrank_euclideanSpace, Fintype.card_fin]
    change ENNReal.ofReal D * 2^k ≤ ENNReal.ofReal (2*R)^k * ENNReal.ofReal U
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      mul_pow, powR, mul_assoc, div_mul_cancel₀ D hU.ne',
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp [mul_comm]
  let : Countable L.toAddSubgroup := (inferInstance : Countable L)
  let : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  obtain ⟨v,hv,hm⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := L.toAddSubgroup) fund (fun x hx ↦ by simpa using hx)
    (convex_closedBall _ _) (isCompact_closedBall _ _) size
  exact ⟨v,hv,by simpa [R,U,D] using hm⟩

private theorem gamma_step {x : ℝ} (hx : 1 ≤ x)
    (h : Real.Gamma (x+1) ≤ ((x+2)/2)^x) :
    Real.Gamma (x+1+1) ≤ ((x+3)/2)^(x+1) := by
  have ha : 0 < (x+2)/2 := by linarith
  have hd : 0 < x+2 := by linarith
  have hb : 0 < (x+3)/2 := by linarith
  have hratio : (x+3)/2 = ((x+2)/2)*(1+1/(x+2)) := by field_simp; ring
  have hbern := one_add_mul_self_le_rpow_one_add
    (s := 1/(x+2)) (by linarith [one_div_pos.mpr hd] : -(1:ℝ) ≤ 1/(x+2)) hx
  have hc : x+1 ≤ (1+x*(1/(x+2)))*((x+3)/2) := by
    field_simp
    nlinarith
  rw [Real.Gamma_add_one (by linarith), Real.rpow_add_one hb.ne']
  calc
    _ ≤ (x+1)*(((x+2)/2)^x) := mul_le_mul_of_nonneg_left h (by linarith)
    _ ≤ ((1+1/(x+2))^x*((x+3)/2))*(((x+2)/2)^x) := by
      gcongr
      exact hc.trans (mul_le_mul_of_nonneg_right hbern hb.le)
    _ = _ := by
      conv_rhs => lhs; rw [hratio, Real.mul_rpow ha.le (by positivity)]
      ring

/-- An elementary half-integer Gamma estimate, using the recurrence and Bernoulli. -/
theorem gamma_half_nat_bound (k : ℕ) :
    Real.Gamma ((k:ℝ)/2+1) ≤ (((k:ℝ)+4)/4)^((k:ℝ)/2) := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one =>
    convert Real.Gamma_three_div_two_lt_one.le.trans
      (Real.one_le_rpow (by norm_num : (1:ℝ) ≤ (1+4)/4) (by norm_num : (0:ℝ) ≤ 1/2)) using 1 <;> norm_num
  | more k ih _ =>
    rcases k with _ | k
    · norm_num [Real.Gamma_two]
    rcases k with _ | k
    · have h := Real.Gamma_three_div_two_lt_one.le
      have h' := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 7/4)
        (by norm_num : (1:ℝ) ≤ 3/2)
      rw [Real.rpow_one] at h'
      convert (show (3/2:ℝ)*Real.Gamma (3/2) ≤ (7/4:ℝ)^(3/2:ℝ) by linarith) using 1
      · convert Real.Gamma_add_one (by norm_num : (3/2:ℝ) ≠ 0) using 2
      · norm_num
    push_cast at ih ⊢
    apply le_of_eq_of_le _ ((gamma_step (x := ((k:ℝ)+1+1)/2) (by linarith [Nat.cast_nonneg (α := ℝ) k])
      (by convert ih using 2; ring)).trans_eq _)
    · congr 1; ring
    · congr 1 <;> ring

/-- Squared-length Minkowski bound with the elementary coefficient (k+4)/π. -/
theorem hermite_ball_linear {k : ℕ} [NeZero k] (L : Submodule ℤ (EuclideanSpace ℝ (Fin k)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v : L, v ≠ 0 ∧ ‖v.val‖^2 ≤ ((k:ℝ)+4)/Real.pi * ZLattice.covolume L^(2/(k:ℝ)) := by
  obtain ⟨v,hv,h⟩ := hermite_ball L
  refine ⟨v,hv,?_⟩
  have hk : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hd := ZLattice.covolume_pos L volume
  have hg := Real.Gamma_pos_of_pos (show 0 < (k:ℝ)/2+1 by positivity)
  have hp := Real.sqrt_pos.2 Real.pi_pos
  have hh := Real.rpow_le_rpow hg.le (gamma_half_nat_bound k)
    (by positivity : (0:ℝ) ≤ 2/k)
  rw [← Real.rpow_mul (by positivity), show (k:ℝ)/2*(2/k) = 1 by field_simp, Real.rpow_one] at hh
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 h
  rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), show (1/(k:ℝ))*(2:ℕ) = 2/k by push_cast; ring,
    div_div_eq_mul_div, Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow hd.le hg.le, ← Real.rpow_natCast (Real.sqrt Real.pi) k, ← Real.rpow_mul hp.le,
    show (k:ℝ)*(2/k) = 2 by field_simp, Real.rpow_two, Real.sq_sqrt Real.pi_pos.le] at hs
  apply hs.trans
  rw [div_mul_eq_mul_div, ← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right Real.pi_pos).2
  nlinarith [mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hd.le (2/k))]

/-- The same bound in ordinary coordinate space with the Euclidean sum of squares. -/
theorem hermite_linear_coords {k : ℕ} [NeZero k] (L : Submodule ℤ (Fin k → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v : L, v ≠ 0 ∧ ∑ i, (v.val i)^2 ≤ ((k:ℝ)+4)/Real.pi * ZLattice.covolume L^(2/(k:ℝ)) := by
  let e := EuclideanSpace.equiv (Fin k) ℝ
  have he : MeasurePreserving e := PiLp.volume_preserving_ofLp (Fin k)
  obtain ⟨v,hv,h⟩ := hermite_ball_linear (ZLattice.comap ℝ L e.toLinearMap)
  refine ⟨⟨e v.val,v.property⟩, ?_, ?_⟩
  · intro hz
    apply hv
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val hz
  · rwa [EuclideanSpace.real_norm_sq_eq, ZLattice.covolume_comap L volume volume he] at h

end SigabaNeo.BKZ

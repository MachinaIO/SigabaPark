import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelDensityTests

set_option autoImplicit true

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace SigabaNeo.Rogers

private abbrev Site {n : ℕ} (g : SL n) := {x : E n // x ∈ points (QuotientGroup.mk g) ∧ x ≠ 0}
private def hits {n : ℕ} (g : SL n) (j : ℕ) : Set (Site g) := {x | x.val ∈ densityBall n j}

private theorem work_eq {n : ℕ} (g : SL n) (j : ℕ) :
    densityWork n j g = (ENat.card (hits g j) : ℝ≥0∞) * (volume (densityBall n j))⁻¹ := by
  classical
  unfold densityWork tupleWorkload
  trans ∑' x : Site g, densityTest n j x.val
  · exact (Equiv.funUnique (Fin 1) (Site g)).tsum_eq (fun x ↦ densityTest n j x.val)
  change (∑' x, (hits g j).indicator (fun _ ↦ (volume (densityBall n j))⁻¹) x) = _
  rw [← tsum_subtype, ENNReal.tsum_const]

private theorem hit_bound {n : ℕ} (g : SL n) (j : ℕ) :
    ENat.card (hits g j) ≤ ((2 * (j+1) : ℕ) : ℕ∞)^n * (1 + ENat.card (hits g 0)) := by
  classical
  let m := 2 * (j+1)
  have hm : 0 < m := by dsimp [m]; omega
  let : NeZero m := ⟨hm.ne'⟩
  let T := g.toLin'.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin n) ℝ).symm
  let emb (z : Fin n → ℤ) := T (fun i ↦ (z i : ℝ))
  have ex (x : hits g j) : ∃ z, emb z = x.val.val := by
    have hx := x.val.property.1
    exact (points_mk g ▸ hx : x.val.val ∈ Set.range (fun a ↦ emb a))
  let z (x : hits g j) := (ex x).choose
  let color (x : hits g j) (i : Fin n) : ZMod m := (z x i : ZMod m)
  let rep (c : Set.range color) := c.property.choose
  have eqc (x : hits g j) : color (rep ⟨color x, x, rfl⟩) = color x :=
    (show color x ∈ Set.range color from ⟨x,rfl⟩).choose_spec
  let base (x : hits g j) := rep ⟨color x, x, rfl⟩
  have splitDiff (x : hits g j) : ∃ y : Fin n → ℤ,
      (m : ℝ) • emb y = x.val.val - (base x).val.val := by
    have hd (i : Fin n) : (m : ℤ) ∣ z x i - z (base x) i := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      rw [Int.cast_sub, sub_eq_zero]
      exact (congrFun (eqc x) i).symm
    choose y hy using hd
    refine ⟨y, ?_⟩
    rw [← (ex x).choose_spec, ← (ex (base x)).choose_spec]
    change _ • T _ = T _ - T _
    rw [← map_smul, ← map_sub]
    congr 1
    ext i
    change (m : ℝ) * (y i : ℝ) = (z x i : ℝ) - (z (base x) i : ℝ)
    exact_mod_cast (hy i).symm
  let diff (x : hits g j) := emb (splitDiff x).choose
  have spec (x : hits g j) : (m : ℝ) • diff x = x.val.val - (base x).val.val :=
    (splitDiff x).choose_spec
  have small (x : hits g j) : diff x ∈ densityBall n 0 := by
    have hx (a : hits g j) : ‖a.val.val‖ < (j : ℝ) + 1 := by
      simpa [hits,densityBall] using a.property
    have h := (norm_sub_le x.val.val (base x).val.val).trans_lt (add_lt_add (hx x) (hx (base x)))
    rw [← spec, norm_smul] at h
    simp [densityBall]
    simp [m, abs_of_nonneg (by positivity : 0 ≤ (j : ℝ)+1)] at h
    nlinarith
  let code (x : hits g j) : Unit ⊕ hits g 0 :=
    if h : diff x = 0 then Sum.inl () else Sum.inr ⟨⟨diff x, by
      rw [points_mk]; exact ⟨_, rfl⟩, h⟩, small x⟩
  let decode : Unit ⊕ hits g 0 → E n := Sum.elim (fun _ ↦ 0) (fun a ↦ a.val.val)
  have dec (x) : decode (code x) = diff x := by
    dsimp [code]; split <;> simp_all [decode]
  have inj : Function.Injective (fun x : hits g j ↦ (color x, code x)) := by
    intro x y he
    have hc := congrArg Prod.fst he
    have hb : base x = base y := congrArg rep (Subtype.ext hc)
    have hd := congrArg decode (congrArg Prod.snd he)
    change decode (code x) = decode (code y) at hd
    rw [dec, dec] at hd
    have hh := spec x
    rw [hd, spec, hb] at hh
    exact Subtype.ext (Subtype.ext (sub_left_inj.mp hh.symm))
  simpa [ENat.card_prod, ENat.card_sum, ENat.card_eq_coe_fintype_card, m] using
    ENat.card_le_card_of_injective inj

theorem siegel_density_residue_class_bound (n : ℕ) (_hn : 2 ≤ n) :
    ∃ C : ℝ≥0, ∀ j g, densityWork n j g ≤ (C : ℝ≥0∞) * (1 + densityWork n 0 g) := by
  let V := volume (Metric.ball (0 : E n) 1)
  have hp : V ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
  let A := (2 : ℝ≥0∞)^n * (1 + V⁻¹)
  have hA : A ≠ ⊤ := by finiteness
  refine ⟨A.toNNReal, fun j g ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hA, work_eq, work_eq]
  let r : ℝ≥0∞ := (j : ℝ≥0∞) + 1
  have hr : r^n ≠ 0 := by dsimp [r]; positivity
  have hrf : r^n ≠ ⊤ := by dsimp [r]; finiteness
  have hv : volume (densityBall n j) = r^n * V := by
    simp [r,V,densityBall,volume.addHaar_ball_of_pos _ (by positivity : 0 < (j : ℝ)+1),
      ENNReal.ofReal_pow (by positivity : 0 ≤ (j : ℝ)+1), ENNReal.ofReal_add (by positivity : 0 ≤ (j : ℝ)) zero_le_one]
  have h0 : volume (densityBall n 0) = V := by simp [densityBall,V]
  have h := ENat.toENNReal_mono (hit_bound g j)
  simp only [ENat.toENNReal_mul, ENat.toENNReal_pow, ENat.toENNReal_coe,
    ENat.toENNReal_add, ENat.toENNReal_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_one, mul_pow] at h
  rw [hv,h0]
  refine (mul_le_mul_left h _).trans ?_
  change 2^n * r^n * (1 + _) * (r^n * V)⁻¹ ≤ _
  rw [ENNReal.mul_inv (Or.inl hr) (Or.inl hrf)]
  generalize (ENat.card (hits g 0) : ℝ≥0∞) = b
  calc
    _ = 2^n * ((1+b)*V⁻¹) * (r^n * (r^n)⁻¹) := by ac_rfl
    _ = 2^n * (V⁻¹ + b*V⁻¹) := by rw [ENNReal.mul_inv_cancel hr hrf, mul_one, add_mul, one_mul]
    _ ≤ A * (1+b*V⁻¹) := by dsimp [A]; rw [mul_assoc]; gcongr; rw [mul_add, mul_one, add_mul, one_mul]; exact add_le_add (le_add_self) (le_self_add)

#print axioms siegel_density_residue_class_bound
end SigabaNeo.Rogers

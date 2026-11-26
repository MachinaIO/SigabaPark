module

public import Definitions.Def_LatticeAttack_Reduction_BKZ
import all Definitions.Def_LatticeAttack_Reduction_BKZ

set_option autoImplicit true

open MeasureTheory Metric Module ZSpan
open scoped RealInnerProductSpace
public section
namespace SigabaNeo.BKZ

/-- Blichfeldt's pointwise packing inequality, in squared-radius units. -/
theorem blichfeldt_mass {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (p : ι → E) {a : ℝ} (ha : 0 ≤ a)
    (sep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2*a ≤ ‖p i - p j‖^2) :
    ∑ i ∈ s, max 0 (a - ‖p i‖^2) ≤ a := by
  classical
  let t := s.filter fun i ↦ 0 ≤ a - ‖p i‖^2
  have mass : ∑ i ∈ s, max 0 (a - ‖p i‖^2) = ∑ i ∈ t, (a - ‖p i‖^2) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with h
    · exact max_eq_right h
    · exact max_eq_left (le_of_not_ge h)
  rw [mass, Finset.sum_sub_distrib]
  by_cases ht : t.Nonempty
  · have pos : (0:ℝ) < t.card := by exact_mod_cast ht.card_pos
    have bound (i) (hi : i ∈ t) :
        (t.card:ℝ)*(2*a) - 2*a ≤ ∑ j ∈ t, ‖p i - p j‖^2 := by
      calc
        _ = ∑ j ∈ t, (if j = i then 0 else 2*a) := by
          simp [Finset.sum_ite, Finset.filter_ne', Finset.card_erase_of_mem hi,
            Nat.cast_sub (Finset.card_pos.mpr ht), mul_comm]; ring
        _ ≤ _ := Finset.sum_le_sum fun j hj ↦ by
          split_ifs with h
          · positivity
          · exact sep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 (Ne.symm h)
    have both := Finset.sum_le_sum bound
    simp only [real_inner_self_eq_norm_sq, norm_sub_sq_real, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← inner_sum, ← sum_inner, Finset.sum_const,
      nsmul_eq_mul] at both
    simp only [Finset.sum_const, nsmul_eq_mul]
    have nn := sq_nonneg ‖∑ i ∈ t, p i‖
    apply le_of_mul_le_mul_left (a := (t.card:ℝ)) _ pos
    nlinarith
  · simp [Finset.not_nonempty_iff_eq_empty.mp ht, ha]

/-- Integrating the periodized quadratic weight over a lattice fundamental domain. -/
theorem blichfeldt_integral {k : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin k)))
    [DiscreteTopology L] [IsZLattice ℝ L] {a : ℝ} (ha : 0 ≤ a)
    (sep : ∀ v : L, v ≠ 0 → 2*a ≤ ‖v.val‖^2) :
    (∫⁻ x : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (a - ‖x‖^2)) ≤
      ENNReal.ofReal a * ENNReal.ofReal (ZLattice.covolume L) := by
  classical
  let b := Free.chooseBasis ℤ L
  let fund : IsAddFundamentalDomain L.toAddSubgroup _ volume := ZLattice.isAddFundamentalDomain b volume
  let : Countable L.toAddSubgroup := (inferInstance : Countable L)
  rw [fund.lintegral_eq_tsum'', ← lintegral_tsum]
  · calc
      _ ≤ ∫⁻ _ in fundamentalDomain (b.ofZLatticeBasis ℝ), ENNReal.ofReal a := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [tsum_eq_iSup_sum]
        apply iSup_le
        intro s
        let p := fun v : L.toAddSubgroup ↦ v.val + x
        have h := blichfeldt_mass s p ha (by
          intro i _ j _ h
          have hd := sep (i-j) (sub_ne_zero.mpr h)
          simpa [p, add_sub_add_right_eq_sub] using hd)
        calc
          _ = ∑ v ∈ s, ENNReal.ofReal (max 0 (a - ‖p v‖^2)) := by
            apply Finset.sum_congr rfl
            intro v _
            simp [ENNReal.ofReal_max, p, AddSubgroup.vadd_def]
          _ = _ := (ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ le_max_left _ _).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal h
      _ = _ := by
        rw [lintegral_const, Measure.restrict_apply_univ,
          ZLattice.covolume_eq_measure_fundamentalDomain L volume fund, Measure.real,
          ENNReal.ofReal_toReal (fundamentalDomain_isBounded _).measure_lt_top.ne]
  · intro i
    change AEMeasurable (fun x ↦ ENNReal.ofReal (a - ‖i.val + x‖^2)) _
    fun_prop

/-- Radial integration of the truncated quadratic on its supporting ball. -/
theorem blichfeldt_radial {k : ℕ} [NeZero k] {R : ℝ} (hR : 0 < R) :
    (∫ x in closedBall (0 : EuclideanSpace ℝ (Fin k)) R, (R^2 - ‖x‖^2)) =
      volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1) * 2 * R^(k+2) / (k+2) := by
  classical
  let E := EuclideanSpace ℝ (Fin k)
  have hk := Nat.pos_of_ne_zero (NeZero.ne k)
  let m := k-1
  have km : k = m+1 := by dsimp [m]; omega
  have rad := integral_fun_norm_addHaar (E := E) volume
    ((Set.Iic R).indicator fun y : ℝ ↦ R^2 - y^2)
  have lhs : (fun x : E ↦ (Set.Iic R).indicator (fun y : ℝ ↦ R^2-y^2) ‖x‖) =
      (closedBall (0:E) R).indicator (fun x ↦ R^2-‖x‖^2) := by
    ext x
    simp [Set.indicator, Metric.mem_closedBall, dist_zero_right]
  rw [show (∫ x : E, (Set.Iic R).indicator (fun y : ℝ ↦ R^2-y^2) ‖x‖) = _ from
    congrArg (fun f : E → ℝ ↦ ∫ x, f x) lhs, integral_indicator measurableSet_closedBall] at rad
  rw [rad]
  simp only [E, finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  have ind : (fun y : ℝ ↦ y^(k-1) * (Set.Iic R).indicator (fun t : ℝ ↦ R^2-t^2) y) =
      (Set.Iic R).indicator (fun y ↦ R^2*y^m-y^(m+2)) := by
    ext y
    by_cases h : y ≤ R <;> simp [Set.indicator, h, m, pow_add]; ring
  rw [show (∫ y in Set.Ioi (0:ℝ), y^(k-1) *
    (Set.Iic R).indicator (fun t : ℝ ↦ R^2-t^2) y) = _ from
    congrArg (fun f : ℝ → ℝ ↦ ∫ y in Set.Ioi (0:ℝ), f y) ind,
    setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic,
    ← intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  · rw [show (k:ℝ) = (m:ℝ)+1 by exact_mod_cast km, show k+2 = m+1+2 by omega]
    push_cast
    simp only [zero_pow (Nat.succ_ne_zero _), sub_zero, pow_succ]
    field_simp
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- Blichfeldt's Hermite bound in every positive dimension. -/
theorem hermite_blichfeldt {k : ℕ} [NeZero k] (L : Submodule ℤ (EuclideanSpace ℝ (Fin k)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v : L, v ≠ 0 ∧ ‖v.val‖^2 ≤ (2/Real.pi) * Real.Gamma ((k:ℝ)/2+2)^(2/(k:ℝ)) *
      ZLattice.covolume L^(2/(k:ℝ)) := by
  let E := EuclideanSpace ℝ (Fin k)
  let : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  have hc : IsClosed (L : Set E) := L.toAddSubgroup.isClosed_of_discreteTopology
  let : ProperSpace L := ProperSpace.of_isClosed hc
  let S : Set L := {v | v ≠ 0}
  obtain ⟨u,hu,_⟩ := hermite_ball L
  obtain ⟨v,hv,eq⟩ := (isClosed_discrete S).exists_infDist_eq_dist ⟨u,hu⟩ (0:L)
  change v ≠ 0 at hv
  refine ⟨v,hv,?_⟩
  have vp : 0 < ‖v.val‖ := norm_pos_iff.mpr fun e ↦ hv (Subtype.ext e)
  let R := ‖v.val‖ / Real.sqrt 2
  have rp : 0 < R := by dsimp [R]; positivity
  have vs : ‖v.val‖^2 = 2*R^2 := by simp [R, div_pow]; ring
  have h := blichfeldt_integral L (sq_nonneg R) (by
    intro w hw
    have hh := infDist_le_dist_of_mem (x := (0:L)) (show w ∈ S from hw)
    rw [eq, dist_zero_left, dist_zero_left] at hh
    exact vs ▸ (sq_le_sq₀ (norm_nonneg v.val) (norm_nonneg w.val)).mpr hh)
  let B := closedBall (0:E) R
  let f := fun x : E ↦ R^2-‖x‖^2
  have fi : IntegrableOn f B := (by fun_prop : Continuous f).continuousOn.integrableOn_compact
    (isCompact_closedBall _ _)
  have nn : 0 ≤ᵐ[volume.restrict B] f := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := B) measurableSet_closedBall] with x hx
    have hx' : ‖x‖ ≤ R := by simpa [B, Metric.mem_closedBall] using hx
    exact sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) rp.le).mpr hx')
  have hh := (ofReal_integral_eq_lintegral_ofReal fi nn).le.trans
    ((lintegral_mono' Measure.restrict_le_self (le_refl (fun x ↦ ENNReal.ofReal (f x)))).trans h)
  change ENNReal.ofReal (∫ x in closedBall (0:E) R, R^2-‖x‖^2) ≤ _ at hh
  rw [blichfeldt_radial rp, ← ENNReal.ofReal_mul (sq_nonneg _)] at hh
  have hd := ZLattice.covolume_pos L volume
  have H := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg R) hd.le)).mp hh
  have hg := Real.Gamma_pos_of_pos (show 0 < (k:ℝ)/2+1 by positivity)
  simp only [Measure.real, EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one,
    one_pow, one_mul, ENNReal.toReal_ofReal (div_nonneg (pow_nonneg (Real.sqrt_nonneg Real.pi) k) hg.le)] at H
  let G := Real.Gamma ((k:ℝ)/2+2)
  have hk : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have gp : 0 < G := Real.Gamma_pos_of_pos (by positivity)
  have ge : G = ((k:ℝ)/2+1)*Real.Gamma ((k:ℝ)/2+1) := by
    dsimp [G]; convert Real.Gamma_add_one (by positivity : (k:ℝ)/2+1 ≠ 0) using 2; ring
  have power : R^k ≤ ZLattice.covolume L * G / (Real.sqrt Real.pi)^k := by
    apply (le_div_iff₀ (by positivity)).2
    rw [ge]
    rw [pow_add] at H
    field_simp at H
    rw [show ((k:ℝ)+2)/2 = k/2+1 by ring] at H
    nlinarith
  have hp := Real.sqrt_pos.2 Real.pi_pos
  have raised := Real.rpow_le_rpow (pow_nonneg rp.le k) power (by positivity : 0 ≤ 2/(k:ℝ))
  rw [← Real.rpow_natCast R, ← Real.rpow_mul rp.le,
    Real.div_rpow (mul_nonneg hd.le gp.le) (pow_nonneg hp.le k), Real.mul_rpow hd.le gp.le,
    ← Real.rpow_natCast (Real.sqrt Real.pi), ← Real.rpow_mul hp.le,
    show (k:ℝ)*(2/k) = 2 by field_simp, Real.rpow_two, Real.rpow_two,
    Real.sq_sqrt Real.pi_pos.le] at raised
  rw [vs]
  dsimp [G] at raised
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left raised (by norm_num : (0:ℝ) ≤ 2)
    _ = _ := by ring
noncomputable def blichfeldtConstant (k : ℕ) : ℝ :=
  (2/Real.pi) * Real.Gamma ((k:ℝ)/2+2)^(2/(k:ℝ))

theorem blichfeldtConstant_pos (k : ℕ) : 0 < blichfeldtConstant k :=
  mul_pos (by positivity) (Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos (by positivity)) _)

/-- Log convexity of Gamma makes the same constant valid on shorter terminal blocks. -/
theorem blichfeldtConstant_mono {k b : ℕ} (hk : 0 < k) (hb : k ≤ b) :
    blichfeldtConstant k ≤ blichfeldtConstant b := by
  have kp : (0:ℝ) < k := by exact_mod_cast hk
  have kb : (k:ℝ) ≤ b := by exact_mod_cast hb
  have h := Real.convexOn_log_Gamma.secant_mono (a := 2) (x := (k:ℝ)/2+2)
    (y := (b:ℝ)/2+2) (by norm_num) (by change 0 < _; positivity) (by change 0 < _; positivity)
    (by linarith) (by linarith) (by linarith)
  simp only [Function.comp_apply, Real.Gamma_two, Real.log_one, sub_zero, add_sub_cancel_right] at h
  unfold blichfeldtConstant
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.rpow_def_of_pos (Real.Gamma_pos_of_pos (by positivity)),
    Real.rpow_def_of_pos (Real.Gamma_pos_of_pos (by positivity)), Real.exp_le_exp]
  convert h using 1 <;> ring

private theorem one_le_blichfeldtConstant {b : ℕ} (hb : 2 ≤ b) : 1 ≤ blichfeldtConstant b := by
  apply le_trans _ (blichfeldtConstant_mono (by decide : 0 < 2) hb)
  norm_num [blichfeldtConstant, Real.Gamma_nat_eq_factorial]
  rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
  linarith [Real.pi_lt_four]

theorem hermite_blichfeldt_coords {k : ℕ} [NeZero k] (L : Submodule ℤ (Fin k → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v : L, v ≠ 0 ∧ ∑ i, (v.val i)^2 ≤ blichfeldtConstant k * ZLattice.covolume L^(2/(k:ℝ)) := by
  let e := EuclideanSpace.equiv (Fin k) ℝ
  have he : MeasurePreserving e := PiLp.volume_preserving_ofLp (Fin k)
  obtain ⟨v,hv,h⟩ := hermite_blichfeldt (ZLattice.comap ℝ L e.toLinearMap)
  refine ⟨⟨e v.val,v.property⟩, ?_, ?_⟩
  · intro hz
    apply hv
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val hz
  · rwa [EuclideanSpace.real_norm_sq_eq, ZLattice.covolume_comap L volume volume he] at h

/-- In dimension one the cube gives coefficient one, while Blichfeldt gives 9/8. -/
theorem hermite_one_improvement (L : Submodule ℤ (Fin 1 → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    (∃ v : L, v ≠ 0 ∧ ∑ i, (v.val i)^2 ≤ ZLattice.covolume L^2) ∧
      blichfeldtConstant 1 = 9/8 := by
  constructor
  · simpa using hermite_cube L
  · unfold blichfeldtConstant
    rw [Nat.cast_one, div_one, Real.rpow_two,
      show (1:ℝ)/2+2 = 1/2+1+1 by ring,
      Real.Gamma_add_one (by norm_num : (1:ℝ)/2+1 ≠ 0),
      Real.Gamma_add_one (by norm_num : (1:ℝ)/2 ≠ 0), Real.Gamma_one_half_eq]
    field_simp
    nlinarith [Real.sq_sqrt Real.pi_pos.le]

open InnerProductSpace
variable {n β : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin n)) (hb : LinearIndependent ℝ b)

private theorem reduced_blichfeldt_profile (hr : Reduced b hb β) (hβ : 2 ≤ β) :
    BlockProfile (basisLog b) n β (Real.log (blichfeldtConstant β)/2) := by
  intro i hi
  let k := min β (n-i)
  have hk : 0 < k := by dsimp [k]; omega
  let : NeZero k := ⟨hk.ne'⟩
  let B := reducedProjectedBlock b hb hr i hi
  let _ := B.discrete
  let _ := B.full
  obtain ⟨v,hv,h⟩ := hermite_blichfeldt_coords B.lattice
  have hp := ZLattice.covolume_pos B.lattice MeasureTheory.volume
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hx := Real.log_le_log (Real.exp_pos _) ((B.shortest v hv).trans h)
  change Real.log (Real.exp _) ≤ Real.log ((blichfeldtConstant k) * _^(2/(k:ℝ))) at hx
  rw [Real.log_exp, Real.log_mul (blichfeldtConstant_pos k).ne' (Real.rpow_pos_of_pos hp _).ne',
    Real.log_rpow hp, B.logCovol] at hx
  have hl := Real.log_le_log (blichfeldtConstant_pos k)
    (blichfeldtConstant_mono hk (min_le_left β (n-i)))
  change (k:ℝ)*basisLog b i ≤ k*(Real.log (blichfeldtConstant β)/2) +
    logPrefix (basisLog b) (i+k) - logPrefix (basisLog b) i
  change 2*basisLog b i ≤ Real.log ((blichfeldtConstant k)) +
    2/(k:ℝ)*(logPrefix (basisLog b) (i+k) - logPrefix (basisLog b) i) at hx
  field_simp at hx
  nlinarith [mul_le_mul_of_nonneg_left hl hk'.le]

theorem reduced_first_norm_bound_covolume_blichfeldt
    (a : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hr : Reduced a a.linearIndependent β) (hβ : 2 ≤ β) (hn : β ≤ n) :
    ‖a ⟨0, by omega⟩‖ ≤ (blichfeldtConstant β) ^ (((n:ℝ)-1)/(2*((β:ℝ)-1))+1/2) *
      ZLattice.covolume (Submodule.span ℤ (Set.range a)) ^ (1/(n:ℝ)) := by
  rw [basis_covolume]
  apply basis_profile_bound a a.linearIndependent _ _ hβ hn
  · exact one_le_blichfeldtConstant hβ
  exact reduced_blichfeldt_profile a a.linearIndependent hr hβ

theorem reduced_approx_factor_blichfeldt (hr : Reduced b hb β) (hβ : 2 ≤ β) (hn : β ≤ n)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ Submodule.span ℤ (Set.range b)) (hne : v ≠ 0) :
    ‖b ⟨0, by omega⟩‖ ≤ (blichfeldtConstant β) ^ (((n:ℝ)-1)/((β:ℝ)-1)) * ‖v‖ := by
  classical
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
  let s := Finset.univ.filter fun j ↦ z j ≠ 0
  have hs : s.Nonempty := by
    by_contra! empty
    apply hne
    rw [← hz]
    apply Finset.sum_eq_zero
    intro j _
    have : z j = 0 := by
      by_contra nz
      have mem : j ∈ s := by simp [s,nz]
      simp [empty] at mem
    simp [this]
  let t := s.max' hs
  have mem := s.max'_mem hs
  change t ∈ s at mem
  have top (j : Fin n) (gt : t < j) : z j = 0 := by
    by_contra nz
    exact gt.not_ge (s.le_max' j (by simp [s,nz]))
  let C := blichfeldtConstant β
  have cp : 0 < C := blichfeldtConstant_pos β
  have cl : 0 ≤ Real.log C := Real.log_nonneg (one_le_blichfeldtConstant hβ)
  have bound := profile_to_column hβ (reduced_blichfeldt_profile b hb hr hβ) t.val t.isLt
    (div_nonneg cl (by norm_num)) (M := Real.log ‖v‖) (by
      intro i hi cover
      have h := covering_block_bound b hb hr z t ⟨i,by omega⟩ (Finset.mem_filter.mp mem).2 top
        hi (by change t.val < i + min β (n-i); omega)
      rw [hz] at h
      simpa [basisLog, show i < n by omega] using
        Real.log_le_log (norm_pos_iff.mpr (gramSchmidt_ne_zero _ hb)) h) 0 (by omega)
  have np : 0 < n := by omega
  let : NeZero n := ⟨np.ne'⟩
  have first : gramSchmidt ℝ b (⟨0,np⟩ : Fin n) = b ⟨0,np⟩ := by
    rw [gramSchmidt_def]
    have he : Finset.Iio (⟨0,np⟩ : Fin n) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun j hj ↦
        Nat.not_lt_zero j.val (show j < (⟨0,np⟩ : Fin n) from Finset.mem_Iio.mp hj)
    rw [he, Finset.sum_empty, sub_zero]
  simp only [basisLog, dite_eq_left np, first, Nat.cast_zero, sub_zero] at bound
  have bp : (1:ℝ) < β := by exact_mod_cast (show 1 < β by omega)
  have tn : (t.val:ℝ)+1 ≤ n := by exact_mod_cast t.isLt
  change ‖b _‖ ≤ C ^ _ * ‖v‖
  rw [Real.rpow_def_of_pos cp, ← Real.exp_log (norm_pos_iff.mpr hne), ← Real.exp_add]
  apply (Real.log_le_iff_le_exp (norm_pos_iff.mpr (hb.ne_zero _))).mp
  change Real.log ‖b _‖ ≤ Real.log ‖v‖ + 2*(Real.log C/2)/_ * _ at bound
  rw [show 2*(Real.log C/2) = Real.log C by ring] at bound
  calc
    _ ≤ _ := bound
    _ ≤ Real.log ‖v‖ + Real.log C/((β:ℝ)-1)*((n:ℝ)-1) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left (by linarith only [tn])
        (div_nonneg cl (sub_nonneg.mpr bp.le))) _
    _ = _ := by ring

#print axioms reduced_first_norm_bound_covolume_blichfeldt
#print axioms reduced_approx_factor_blichfeldt
#print axioms hermite_one_improvement
#print axioms hermite_blichfeldt
#print axioms blichfeldt_radial
#print axioms blichfeldt_integral
#print axioms blichfeldt_mass
end SigabaNeo.BKZ

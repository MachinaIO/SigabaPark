import Definitions.Def_LatticeAttack_Research_Wall1_HermiteLens506
import Definitions.Def_LatticeAttack_Research_Wall1_ControlledConcreteBounds

set_option autoImplicit true

/-! Reduction of the physical floor to sphere and thin-shell inequalities.
All integrals in the reduction use the actual lattice and its fundamental domain. -/

noncomputable section
namespace SigabaNeo.Wall1.HermiteWitness506

open Real MeasureTheory Metric Finset TerminalProjection
open scoped RealInnerProductSpace Classical Pointwise

set_option maxRecDepth 6000

abbrev Space := EuclideanSpace ℝ (Fin 506)

/-- Spherical addition-formula inequality, with the two sums including the diagonal. -/
def SphericalPairLower : Prop :=
  ∀ {ι : Type} (S : Finset ι) (u : ι → Space), (∀ i ∈ S, ‖u i‖ = 1) →
    (fZero:ℝ) * (S.card:ℝ)^2 ≤ ∑ i ∈ S, ∑ j ∈ S, sphericalKernel ⟪u i,u j⟫

/-- Signed integral in the only displacement range left by the pointwise sign. -/
def ThinShellSign : Prop :=
  ∀ (s : ℝ) (w : Space), 0 < s → s ≤ ‖w‖ →
    ‖w‖^2 < 2*(1-(threshold:ℝ))*(radiusSq:ℝ)*s^2 →
    (∫ x, lens (√(radiusSq:ℝ)*s) w x) ≤ 0

private theorem kernel_one : sphericalKernel 1 =
    ((∑ j ∈ range 32, q j) * (∑ j ∈ range 33, v j) : ℚ) := by
  have h (j : ℕ) : zonalPair 1 j = (1,1) := by
    induction j with
    | zero => rfl
    | succ j ih => simp [zonalPair,ih]; field_simp; ring
  have eqn : ∑ j ∈ range 33, v j = (1-threshold) * ∑ j ∈ range 32, q j := by
    decide +kernel
  rw [eqn,sphericalKernel,sphericalFactor]
  simp only [h,mul_one,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_sum]
  ring

private theorem finite_shifts (L : Submodule ℤ Space) [DiscreteTopology L] (b : ℝ) :
    {a : L | ‖(a:Space)‖ ≤ b}.Finite := by
  have hf : (closedBall (0:Space) b ∩ (L:Set Space)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete Metric.isBounded_closedBall
      L.toAddSubgroup.isClosed_of_discreteTopology
  exact (hf.preimage (f:=((↑) : L → Space)) Subtype.val_injective.injOn).subset
    (fun a h ↦ ⟨mem_closedBall_zero_iff.mpr h,a.property⟩)

private def shifts (L : Submodule ℤ Space) [DiscreteTopology L] (b : ℝ) : Finset L :=
  (finite_shifts L b).toFinset

private theorem mem_shifts {L : Submodule ℤ Space} [DiscreteTopology L] (b : ℝ) (a : L) :
    a ∈ shifts L b ↔ ‖(a:Space)‖ ≤ b := by
  unfold shifts
  exact Set.Finite.mem_toFinset _

private theorem translated_integrable {f : Space → ℝ} (hf : Integrable f) (z : Space) :
    Integrable (fun x ↦ f (z+x)) :=
  ((measurePreserving_add_left volume z).integrable_comp hf.aestronglyMeasurable).2 hf

private theorem unfold_finite {L : Submodule ℤ Space} [DiscreteTopology L] [IsZLattice ℝ L]
    {A : Set Space} (hA : IsAddFundamentalDomain L.toAddSubgroup A volume) (hm : MeasurableSet A)
    (S : Finset L) {f : Space → ℝ} (hf : Integrable f)
    (support : ∀ a ∉ S, ∀ x ∈ A, f ((a:Space)+x) = 0) :
    (∫ x in A, ∑ a ∈ S, f ((a:Space)+x)) = ∫ x, f x := by
  let : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  rw [integral_finsetSum S (f:=fun a x ↦ f ((a:Space)+x)) fun a _ ↦ (translated_integrable hf a).integrableOn]
  rw [hA.integral_eq_tsum'' f hf]
  symm
  apply tsum_eq_sum
  intro a ha
  calc _ = ∫ _ : Space in A, (0:ℝ) := setIntegral_congr_fun hm (fun x hx ↦ support a ha x hx)
       _ = 0 := by simp

private theorem unit_inner (a b : Space) :
    ⟪‖a‖⁻¹ • a, ‖b‖⁻¹ • b⟫ = ⟪a,b⟫ / (‖a‖*‖b‖) := by
  rw [real_inner_smul_left,real_inner_smul_right]; ring

/-- Expand the ordered pair sum at a given center by its signed displacement. -/
private theorem split_pairs {L : Submodule ℤ Space} (S : Finset L) (x : Space) (R : ℝ)
    (support : ∀ a : L, ‖(a:Space)+x‖ < R → a ∈ S)
    (hne : ∀ a ∈ S, (a:Space)+x ≠ 0) (sphere : SphericalPairLower) :
    let T : Finset L := S.filter (fun (a : L) ↦ ‖(a:Space)+x‖ < R)
    let D := (S-S).erase 0
    (fZero:ℝ)*(T.card:ℝ)^2 ≤ sphericalKernel 1*T.card +
      ∑ d ∈ D, ∑ a ∈ S, lens R (d:Space) ((a:Space)+x) := by
  intro T D
  let u (a : L) := ‖(a:Space)+x‖⁻¹ • ((a:Space)+x)
  have hu (a : L) (ha : a ∈ T) : ‖u a‖ = 1 := by
    have hz := norm_pos_iff.mpr (hne a (mem_filter.mp ha).1)
    dsimp only [u]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hz),inv_mul_cancel₀ hz.ne']
  apply (sphere T u hu).trans_eq
  have row (a : L) (ha : a ∈ T) :
      ∑ b ∈ T, sphericalKernel ⟪u a,u b⟫ =
        sphericalKernel 1 + ∑ d ∈ D, lens R (d:Space) ((a:Space)+x) := by
    have hd (b : L) (hb : b ∈ T.erase a) : b-a ∈ D :=
      mem_erase.mpr ⟨sub_ne_zero.mpr (mem_erase.mp hb).1,
        Finset.sub_mem_sub ((mem_filter.mp (mem_erase.mp hb).2).1) (mem_filter.mp ha).1⟩
    have add (b : L) : (a:Space)+x+((b-a:L):Space) = (b:Space)+x := by push_cast; abel
    have other : ∑ b ∈ T.erase a, sphericalKernel ⟪u a,u b⟫ =
        ∑ d ∈ D, lens R (d:Space) ((a:Space)+x) := by
      let I := (T.erase a).image (fun b ↦ b-a)
      calc _ = ∑ d ∈ I, lens R (d:Space) ((a:Space)+x) := by
                  rw [sum_image (fun b _ c _ he ↦ sub_left_injective he)]
                  apply sum_congr rfl
                  intro b hb
                  have hb' := (mem_filter.mp (mem_erase.mp hb).2).2
                  rw [lens,add b,ite_eq_left ⟨(mem_filter.mp ha).2,hb'⟩]
                  exact congrArg sphericalKernel (unit_inner ..)
           _ = _ := by
                  apply sum_subset (fun d h ↦ by obtain ⟨b,hb,rfl⟩ := mem_image.mp h; exact hd b hb)
                  intro d hd' hi
                  have no : ¬ ‖(a:Space)+x+(d:Space)‖ < R := by
                    intro yes
                    have eq : (a:Space)+x+(d:Space) = ((a+d:L):Space)+x := by push_cast; abel
                    have ht : a+d ∈ T := mem_filter.mpr ⟨support _ (eq ▸ yes),eq ▸ yes⟩
                    apply hi
                    exact mem_image.mpr ⟨a+d,mem_erase.mpr
                      ⟨fun he ↦ (mem_erase.mp hd').1 (by simpa using he),ht⟩,by abel⟩
                  simp [lens,no]
    rw [← sum_erase_add T _ ha,other,real_inner_self_eq_norm_sq,hu a ha,one_pow,add_comm]
  rw [sum_congr rfl row,Finset.sum_add_distrib]
  simp only [sum_const,nsmul_eq_mul,mul_comm (T.card:ℝ)]
  apply congrArg (sphericalKernel 1*(T.card:ℝ) + ·)
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  apply sum_subset (filter_subset ..)
  intro a ha ha'
  have short : ¬ ‖(a:Space)+x‖ < R := fun e ↦ ha' (mem_filter.mpr ⟨ha,e⟩)
  simp [lens,short]


/-- The normalized translated-ball moments yield the physical cap from the two
geometric inequalities. The finite index sets depend only on the chosen fundamental domain. -/
theorem shortest_cap_of_sphere_shell (sphere : SphericalPairLower) (shell : ThinShellSign)
    (L : Submodule ℤ Space) [DiscreteTopology L] [IsZLattice ℝ L] {z : Space}
    (hz : DecoupledDecoder.IsShortest L z) :
    ‖z‖^2 ≤ 56.2142 * ZLattice.covolume L ^ (2/(506:ℝ)) := by
  let s := ‖z‖
  let R := √(radiusSq:ℝ)*s
  have hs : 0 < s := norm_pos_iff.mpr hz.2.1
  have hsq : 0 < (radiusSq:ℝ) := by norm_num [radiusSq]
  have hR : 0 < R := mul_pos (sqrt_pos.mpr hsq) hs
  have hR2 : R^2 = (radiusSq:ℝ)*s^2 := by rw [show R = √(radiusSq:ℝ)*s from rfl,mul_pow,sq_sqrt hsq.le]
  let basis := Module.Free.chooseBasis ℤ L
  let basisR := Module.Basis.ofZLatticeBasis ℝ L basis
  let A := ZSpan.fundamentalDomain basisR
  have hA : IsAddFundamentalDomain L.toAddSubgroup A volume :=
    ZLattice.isAddFundamentalDomain basis volume
  have meas := ZSpan.fundamentalDomain_measurableSet basisR
  have bounded := ZSpan.fundamentalDomain_isBounded basisR
  have fin : volume A ≠ ⊤ := bounded.measure_lt_top.ne
  have hd : ZLattice.covolume L = volume.real A :=
    ZLattice.covolume_eq_measure_fundamentalDomain L volume hA
  have positive : volume A ≠ 0 := by
    intro e
    have h := ZLattice.covolume_pos L volume
    rw [hd,Measure.real,e,ENNReal.toReal_zero] at h
    exact lt_irrefl _ h
  obtain ⟨b,hb⟩ := bounded.subset_closedBall (0:Space)
  let S := shifts L (R+b)
  let D := (S-S).erase 0
  have support (x : Space) (hx : x ∈ A) (a : L) (ha : ‖(a:Space)+x‖ < R) : a ∈ S := by
    apply (mem_shifts ..).2
    have H := norm_sub_le ((a:Space)+x) x
    rw [add_sub_cancel_right] at H
    exact H.trans (add_le_add ha.le (mem_closedBall_zero_iff.mp (hb hx)))
  let I : Space → ℝ := (ball (0:Space) R).indicator 1
  have hI : Integrable I := (integrable_indicator_iff measurableSet_ball).2
    (integrableOn_const measure_ball_lt_top.ne)
  let N (x : Space) : ℝ := ∑ a ∈ S, I ((a:Space)+x)
  have card (x : Space) : N x = ((S.filter (fun a : L ↦ ‖(a:Space)+x‖ < R)).card:ℝ) := by
    simp only [N,I,Set.indicator,mem_ball_zero_iff,Pi.one_apply,card_filter,
      Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have mean : (∫ x in A, N x) = volume.real (ball (0:Space) R) := by
    refine (unfold_finite hA meas S hI ?_).trans (integral_indicator_one measurableSet_ball)
    intro a ha x hx
    exact Set.indicator_of_notMem (fun e ↦ ha (support x hx a (mem_ball_zero_iff.mp e))) _
  have hN : Integrable N := integrable_finsetSum S (fun a _ ↦ translated_integrable hI a)
  have hN2 : IntegrableOn (fun x ↦ N x ^ 2) A := by
    apply IntegrableOn.of_bound (lt_top_iff_ne_top.mpr fin) (hN.integrableOn.aestronglyMeasurable.pow 2) (S.card^2:ℝ)
    apply ae_of_all
    intro x
    change ‖N x ^ 2‖ ≤ (S.card:ℝ)^2
    rw [card,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast card_filter_le ..) 2
  let off (d : L) (x : Space) := ∑ a ∈ S, lens R (d:Space) ((a:Space)+x)
  have ho (d : L) : Integrable (off d) := integrable_finsetSum S
    (fun a _ ↦ translated_integrable (lens_integrable R (d:Space)) a)
  have hoff (d : L) (hd' : d ∈ D) : (∫ x in A, off d x) ≤ 0 := by
    rw [show (∫ x in A, off d x) = ∫ x, lens R (d:Space) x from
      unfold_finite hA meas S (lens_integrable R (d:Space)) (fun a ha x hx ↦ by
        have no : ¬ ‖(a:Space)+x‖ < R := fun e ↦ ha (support x hx a e)
        simp [lens,no])]
    by_cases hfar : 2*(1-(threshold:ℝ))*R^2 ≤ ‖(d:Space)‖^2
    · exact integral_nonpos (lens_nonpos_of_separation hfar)
    · have hdn : d ≠ 0 := (mem_erase.mp hd').1
      apply shell s d hs (hz.2.2 d d.property (fun he ↦ hdn (Subtype.ext he)))
      rw [hR2] at hfar
      linarith [lt_of_not_ge hfar]
  let : Countable L := inferInstance
  have avoids : ∀ᵐ x : Space ∂volume, ∀ a : L, (a:Space)+x ≠ 0 := by
    apply ae_all_iff.mpr
    intro a
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (-(a:Space)))] with x hx
    exact fun e ↦ hx (by simpa using (eq_neg_of_add_eq_zero_right e))
  have pair := integral_mono_ae (hN2.const_mul (fZero:ℝ))
    ((hN.integrableOn.const_mul (sphericalKernel 1)).add
      (integrable_finsetSum D (fun d _ ↦ (ho d).integrableOn)))
    (by
      filter_upwards [ae_restrict_mem (μ:=volume) meas,ae_restrict_of_ae avoids] with x hx hn
      simpa only [Pi.add_apply,card,off,D] using split_pairs S x R (support x hx) (fun a _ ↦ hn a) sphere)
  simp only [Pi.add_apply] at pair
  rw [integral_const_mul,integral_add (hN.integrableOn.const_mul _) (integrable_finsetSum D (fun d _ ↦ (ho d).integrableOn)),
    integral_const_mul,integral_finsetSum D (fun d _ ↦ (ho d).integrableOn)] at pair
  have hp : (fZero:ℝ)*(∫ x in A, N x^2) ≤ sphericalKernel 1*(∫ x in A, N x) :=
    pair.trans (add_le_of_nonpos_right (sum_nonpos hoff))
  let μ := (volume A)⁻¹ • volume.restrict A
  let : IsProbabilityMeasure μ := ⟨by
    simp [μ,Measure.smul_apply,Measure.restrict_apply,ENNReal.inv_mul_cancel positive fin]⟩
  have hi {f : Space → ℝ} (hf : IntegrableOn f A volume) : Integrable f μ :=
    (integrable_smul_measure (ENNReal.inv_ne_zero.mpr fin) (ENNReal.inv_ne_top.mpr positive)).2 hf
  have avg (f : Space → ℝ) : (∫ x, f x ∂μ) = (∫ x in A, f x) / ZLattice.covolume L := by
    dsimp only [μ]
    rw [integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,hd,Measure.real]; ring
  apply shortest_cap_of_ball_moments μ N (hi hN.integrableOn) (hi hN2) hs (ZLattice.covolume_pos L volume)
  · rw [avg,mean,Measure.real,Measure.addHaar_ball_of_pos volume _ hR]
    simp only [show Module.finrank ℝ Space = 506 from finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hR.le 506)]
    rw [show R^506 = (R^2)^253 by ring,hR2,mul_pow]
    unfold terminalBallVolume Measure.real
    ring
  · rw [avg,avg,← kernel_one,← mul_div_assoc,← mul_div_assoc]
    exact div_le_div_of_nonneg_right hp (ZLattice.covolume_pos L volume).le

theorem laterFloor_of_sphere_shell (sphere : SphericalPairLower) (shell : ThinShellSign) :
    ControlledPlane.LaterDeterminantFloor := by
  apply ControlledPlane.laterFloor_of_hermite
  intro h j hj
  let P := Restart506.path h
  let i : Fin 406 := ⟨j,by omega⟩
  let := P.discrete i
  let := P.lattice i
  have H := shortest_cap_of_sphere_shell sphere shell (P.window i) (P.shortest i)
  rw [← P.covol i] at H
  exact H

end SigabaNeo.Wall1.HermiteWitness506

#print axioms SigabaNeo.Wall1.HermiteWitness506.shortest_cap_of_sphere_shell
#print axioms SigabaNeo.Wall1.HermiteWitness506.laterFloor_of_sphere_shell

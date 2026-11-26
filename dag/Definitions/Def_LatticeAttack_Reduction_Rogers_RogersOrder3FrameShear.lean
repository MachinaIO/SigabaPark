import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKShear

set_option autoImplicit true

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace SigabaNeo.Rogers.Frame

private def minor {n} (i j k : Fin n) (x : FrameSpace n 3) : ℝ :=
  x 0 i * (x 1 j * x 2 k - x 2 j * x 1 k) +
  x 1 i * (x 2 j * x 0 k - x 0 j * x 2 k) +
  x 2 i * (x 0 j * x 1 k - x 1 j * x 0 k)

private lemma rotate {n} (i j k : Fin n) (x : FrameSpace n 3) :
    minor i j k x = minor j k i x := by unfold minor; ring

private lemma minor_spread {n} {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    [IsFiniteMeasureOnCompacts (frameMeasure (k := 3) D)]
    (i j k l : Fin n) (hij : i ≠ j) (hik : i ≠ k) :
    ∀ᵐ x ∂frameMeasure D, minor i j k x = 0 → minor l j k x = 0 := by
  classical
  by_cases hil : i = l
  · subst l; simp
  let μ := frameMeasure (k := 3) D
  let S (t : ℝ) := {x : FrameSpace n 3 | minor l j k x ≠ 0 ∧ minor i j k x = t * minor l j k x}
  have mm (a b c : Fin n) : Measurable (minor a b c) := by unfold minor; fun_prop
  have hm (t : ℝ) : MeasurableSet (S t) :=
    ((mm l j k (measurableSet_singleton 0)).compl).inter
      (measurableSet_eq_fun (mm i j k) (measurable_const.mul (mm l j k)))
  have disj : Pairwise (fun s t ↦ Disjoint (S s) (S t)) := by
    intro s t h
    exact Set.disjoint_left.mpr fun x hx hy ↦ h (mul_right_cancel₀ hx.1 (hx.2.symm.trans hy.2))
  obtain ⟨t,ht⟩ : ∃ t, μ (S t) = 0 := by
    by_contra! h
    exact Set.not_countable_univ (α := ℝ)
      ((Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) hm disj).mono
        (fun t _ ↦ bot_lt_iff_ne_bot.mpr (h t)))
  have hz : μ (shear i l t ⁻¹' S t) = 0 := by
    rw [← Measure.map_apply (shear_meas _ _ _) (hm t)]
    simpa only [μ, shear_inv hd hil] using ht
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx h
  by_contra hh
  apply hx
  change minor l j k _ ≠ 0 ∧ minor i j k _ = _
  simp only [minor, shear_eval, ite_eq_right (Ne.symm hil), ite_eq_right hij.symm, ite_eq_right hik.symm,
    eq_self, ite_true, zero_add] at *
  exact ⟨hh, by linear_combination h⟩

private lemma exists_minor {n} (x : FrameSpace n 3) (hx : LinearIndependent ℝ x) :
    ∃ i j k, minor i j k x ≠ 0 := by
  by_contra! hall
  obtain ⟨j,hj⟩ : ∃ j, x 0 j ≠ 0 := by
    by_contra! h
    exact hx.ne_zero 0 (by ext a; simpa using h a)
  obtain ⟨k,hk⟩ : ∃ k, x 0 j * x 1 k - x 1 j * x 0 k ≠ 0 := by
    by_contra! h
    apply hj
    apply Fintype.linearIndependent_iff.mp hx ![-x 1 j, x 0 j, 0] _ 1
    ext a
    simp [Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply]
    linear_combination h a
  apply hk
  apply Fintype.linearIndependent_iff.mp hx
    ![x 1 j * x 2 k - x 2 j * x 1 k, x 2 j * x 0 k - x 0 j * x 2 k,
      x 0 j * x 1 k - x 1 j * x 0 k] _ 2
  ext a
  simp [Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply]
  unfold minor at hall
  linear_combination hall a j k

private lemma minor_nonzero_ae {n} {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    [IsFiniteMeasureOnCompacts (frameMeasure (k := 3) D)]
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∀ᵐ x ∂frameMeasure D, minor i j k x ≠ 0 := by
  have spread : ∀ᵐ x ∂frameMeasure D, ∀ a b c d, a ≠ b → a ≠ c →
      minor a b c x = 0 → minor d b c x = 0 := by
    simp only [ae_all_iff]
    intro a b c d
    by_cases h : a = b <;> by_cases g : a = c <;> simp [h,g,minor_spread hd a b c d]
  filter_upwards [spread, frameMeasure_ae_independent (k := 3) D] with x hs hx h
  obtain ⟨a,b,c,habc⟩ := exists_minor x hx
  have one (u) := hs i j k u hij hik h
  have two (u v : Fin n) : minor v k u x = 0 := by
    by_cases hu : j = u
    · subst u
      have H := one v
      unfold minor at *
      linear_combination -H
    · exact hs j k u v hjk hu ((rotate u j k x).symm.trans (one u))
  by_cases hka : k = a
  · subst a; exact habc ((rotate k b c x).trans ((rotate b c k x).trans (two b c)))
  by_cases hkb : k = b
  · subst b; exact habc (two c a)
  exact habc ((rotate a b c x).trans ((rotate b c a x).trans
    (hs k a b c hka hkb ((rotate b k a x).symm.trans (two a b)))))

/-- The independent triple-frame measure is proportional to Lebesgue measure. -/
theorem tripleFrame_proportional {n} (hn : 3 < n) {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤) :
    ∃ C : ℝ≥0∞, frameMeasure (k := 3) D = C • Measure.pi (fun _ ↦ volume) := by
  classical
  let := frameMeasure_finiteOnCompacts (by decide : 0 < 3) hn hd hf
  apply frameMeasure_proportional_of_row (by decide) hn hd hf
  intro i v S
  obtain ⟨j,hji,_⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega)
  obtain ⟨k,hki,hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  have hc : ({i,j,k} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    simp [Finset.card_insert_of_notMem, Ne.symm hji, Ne.symm hki, Ne.symm hkj, hn]
  obtain ⟨l,_,hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  obtain ⟨hli,hlj,hlk⟩ := hl
  let num (b c : Fin n) (x : FrameSpace n 3) :=
    v 0 * (x 1 b * x 2 c - x 2 b * x 1 c) +
    v 1 * (x 2 b * x 0 c - x 0 b * x 2 c) +
    v 2 * (x 0 b * x 1 c - x 1 b * x 0 c)
  let p (a : Fin n) (x : FrameSpace n 3) :=
    ((if a = j then num k l x else 0) + (if a = k then num l j x else 0) +
     (if a = l then num j k x else 0)) / minor j k l x
  apply row_translate_of_coefficients hd i v p _ _ _ S
  · intro a
    dsimp [p, num, minor]
    split_ifs <;> fun_prop
  · intro a x y he
    simp only [p, num, minor, he _ j hji, he _ k hki, he _ l hli]
  · filter_upwards [minor_nonzero_ae hd j k l hkj.symm (Ne.symm hlj) (Ne.symm hlk)] with x hx
    intro a
    simp only [p, add_div, add_mul, ite_div, zero_div, ite_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_erase, Finset.mem_univ, and_true]
    simp [hji,hki,hli]
    field_simp [hx]
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl <;>
      unfold num minor <;> ring

end SigabaNeo.Rogers.Frame

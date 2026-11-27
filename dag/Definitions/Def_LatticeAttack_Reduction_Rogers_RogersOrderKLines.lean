import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKSplit
import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelPrimitiveContent

import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelAssemblyUnfolding

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

theorem lineDiagram_row_card {k q} (A : Diagram 1 k (q+1)) :
    Nat.card (rowImage A) = q+1 := by
  let f : ZMod (q+1) →+ (Fin k → ZMod (q+1)) :=
    { toFun := fun t j ↦ t * (A.entry 0 j : ZMod (q+1))
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp [add_mul] }
  have h : rowImage A ≤ f.range := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    obtain rfl := Subsingleton.elim i 0
    exact ⟨1, by ext; simp [f]⟩
  apply le_antisymm _ (Nat.le_of_dvd Nat.card_pos (denominator_dvd_rowIndex A))
  have h₁ := Nat.card_le_card_of_injective _ (AddSubgroup.inclusion_injective h)
  have h₂ := Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective
  exact h₁.trans (by simpa using h₂)

theorem lineDiagram_weight (n k q : ℕ) (A : Diagram 1 (k+1) (q+1)) :
    congruenceCoefficient n (k+1) 0 q A = dilationWeight n q := by
  simp [congruenceCoefficient, lineDiagram_row_card, dilationWeight, abs_of_nonneg (by positivity : 0 ≤ (q : ℝ) + 1)]

def integerLineTuple {q n k : ℕ} (A : Diagram 1 (k+1) (q+1)) (x : E n) : Fin (k+1) → E n :=
  fun j ↦ (A.entry 0 j : ℝ) • x

theorem rankDiagramTerm_zero (n k : ℕ) (F : (Fin (k+1) → E n) → ℝ≥0∞) (hf : Measurable F) :
    rankDiagramTerm F 0 = ∑' q, ∑' A : Diagram 1 (k+1) (q+1), ∫⁻ x, F (integerLineTuple A x) := by
  unfold rankDiagramTerm
  simp only [Fin.val_zero, Nat.reduceAdd]
  apply tsum_congr
  intro q
  apply tsum_congr
  intro A
  let u := fun x : E n ↦ F (fun j ↦ ((q+1 : ℕ) : ℝ)⁻¹ • (A.entry 0 j : ℝ) • x)
  have hu : Measurable u := hf.comp (Measurable.of_eval (fun j ↦ (measurable_const_smul _).comp (measurable_const_smul (A.entry 0 j : ℝ))))
  rw [lineDiagram_weight]
  change dilationWeight n q * (∫⁻ v : Fin 1 → E n, F (fun j ↦ ((q+1 : ℕ) : ℝ)⁻¹ • ∑ i : Fin 1, (A.entry i j : ℝ) • v i) ∂Measure.pi (fun _ ↦ volume)) = _
  simp only [Fin.sum_univ_one]
  change dilationWeight n q * (∫⁻ v : Fin 1 → E n, u ((MeasurableEquiv.funUnique (Fin 1) (E n)) v) ∂Measure.pi (fun _ ↦ volume)) = _
  refine (congrArg (dilationWeight n q * ·)
    ((measurePreserving_funUnique (volume : Measure (E n)) (Fin 1)).lintegral_comp_emb
      (MeasurableEquiv.funUnique (Fin 1) (E n)).measurableEmbedding u)).trans ?_
  refine (lintegral_dilation q u hu).symm.trans ?_
  apply lintegral_congr
  intro x
  apply congrArg F
  funext j
  change ((q+1 : ℕ) : ℝ)⁻¹ • (A.entry 0 j : ℝ) • ((q+1 : ℕ) : ℝ) • x = (A.entry 0 j : ℝ) • x
  rw [smul_comm (A.entry 0 j : ℝ), inv_smul_smul₀ (by positivity)]

theorem rankOne_siegel_lines (n k : ℕ) (hn : 1 < n) (D : Set (SL n))
    (hD : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤)
    (F : (Fin (k+1) → E n) → ℝ≥0∞) (hf : Measurable F) :
    (∑' q, ∑' A : Diagram 1 (k+1) (q+1), ∑' z : NonzeroIntVector n,
      vectorOrbitalIntegral D (fun x ↦ F (integerLineTuple A x)) z) =
      groupHaar n D * rankDiagramTerm F 0 := by
  let := groupHaar_rightInvariant n
  let : BorelSpace (SL n) := ⟨rfl⟩
  obtain ⟨T, hsub, hm, he⟩ := hD.nullMeasurableSet.exists_measurable_superset_ae_eq
  have ht : IsFundamentalDomain (integerGroup n).op T (groupHaar n) := {
    nullMeasurableSet := hm.nullMeasurableSet
    ae_covers := hD.ae_covers.mono fun _ ⟨g,hg⟩ ↦ ⟨g,hsub hg⟩
    aedisjoint := by
      intro a b hab
      exact (hD.aedisjoint hab).congr ((smul_set_ae_eq a.val).mpr he)
        ((smul_set_ae_eq b.val).mpr he) }
  rw [rankDiagramTerm_zero n k F hf, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro q
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro A
  let u := fun x : E n ↦ F (integerLineTuple A x)
  have hu : Measurable u := hf.comp (Measurable.of_eval fun j ↦ measurable_const_smul _)
  have horb := (domain_lintegral_tupleWorkload (groupHaar n) D
    (F := fun v : Fin 1 → E n ↦ u (v 0)) (hu.comp (measurable_pi_apply 0))).trans
    ((Equiv.funUnique (Fin 1) (NonzeroIntVector n)).tsum_eq (vectorOrbitalIntegral D u))
  refine horb.symm.trans ?_
  rw [← Measure.restrict_congr_set he, ← measure_congr he]
  exact siegel_domain_unfolding_evaluation n (by omega) T hm ht
    (by simpa only [measure_congr he] using hfin) u hu

end SigabaNeo.Rogers

import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder2Split
import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelPrimitiveContent

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

theorem orderTwo_row_card (q : ℕ) (A : Diagram 1 2 (q + 1)) :
    Nat.card (rowImage A) = q + 1 := by
  let ev := Pi.evalAddMonoidHom (fun _ : Fin 2 ↦ ZMod (q + 1)) 0
  have hp : A.pivot 0 = 0 := Fin.ext (A.first 0 rfl)
  have hker : rowImage A ≤ ev.ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change (A.entry i 0 : ZMod (q + 1)) = 0
    rw [← hp, A.pivotColumn, Subsingleton.elim i 0]
    simp only [ite_true, Int.cast_natCast]; exact ZMod.natCast_self _
  have hinj : Function.Injective (fun x : rowImage A ↦ x.val 1) := by
    intro x y he
    apply Subtype.ext
    funext j
    fin_cases j
    · exact (show x.val 0 = 0 from hker x.property).trans
        (show y.val 0 = 0 from hker y.property).symm
    · exact he
  apply le_antisymm _ (Nat.le_of_dvd Nat.card_pos (denominator_dvd_rowIndex A))
  simpa using Nat.card_le_card_of_injective _ hinj

theorem orderTwo_line_weight (n q : ℕ) (A : Diagram 1 2 (q+1)) :
    congruenceCoefficient n 2 0 q A = dilationWeight n q := by
  simp [congruenceCoefficient, orderTwo_row_card, dilationWeight, abs_of_nonneg (by positivity : 0 ≤ (q : ℝ) + 1)]

def orderTwoLine {q n : ℕ} (A : Diagram 1 2 (q+1)) (x : E n) : Fin 2 → E n :=
  fun j ↦ (A.entry 0 j : ℝ) • x

theorem orderTwo_rank_one (n : ℕ) (F : (Fin 2 → E n) → ℝ≥0∞) (hf : Measurable F) :
    orderTwoRankTerm F 0 = ∑' q, ∑' A : Diagram 1 2 (q+1), ∫⁻ x, F (orderTwoLine A x) := by
  unfold orderTwoRankTerm
  simp only [Fin.val_zero, Nat.reduceAdd]
  apply tsum_congr
  intro q
  apply tsum_congr
  intro A
  let u := fun x : E n ↦ F (fun j ↦ ((q+1 : ℕ) : ℝ)⁻¹ • (A.entry 0 j : ℝ) • x)
  have hu : Measurable u := hf.comp (Measurable.of_eval (fun j ↦ (measurable_const_smul _).comp (measurable_const_smul (A.entry 0 j : ℝ))))
  rw [orderTwo_line_weight]
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

end SigabaNeo.Rogers

module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnCoordinates

set_option autoImplicit true

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal
namespace SigabaNeo.Rogers

abbrev ColumnParameters (d : ℕ) := (Fin d → ℝ) × (UpperEntry (d+1) → ℝ)

/-- Logarithmic successive diagonal ratios and upper entries of a column KAU factorization. -/
def HasColumnParameters {d : ℕ} (g : SL (d+1)) (p : ColumnParameters d) : Prop :=
  ∃ (k u : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (a : Fin (d+1) → ℝ),
    k.transpose * k = 1 ∧ (∀ i, 0 < a i) ∧
    (∀ i, u i i = 1) ∧ (∀ i j, j < i → u i j = 0) ∧ g.val = k * Matrix.diagonal a * u ∧
    (fun i : Fin d ↦ Real.log (a i.succ) - Real.log (a i.castSucc)) = p.1 ∧
    (fun i : UpperEntry (d+1) ↦ u i.val.1 i.val.2) = p.2

def columnRootMeasure (d : ℕ) : Measure (Fin d → ℝ) :=
  (Measure.pi fun _ ↦ volume).withDensity fun t ↦ ENNReal.ofReal
    (∏ i, Real.exp (-((i.val + 1 : ℕ) * ((d - i.val : ℕ) : ℝ)) * t i))

theorem columnRootMeasure_tail (d : ℕ) (b : ℝ) :
    columnRootMeasure d (univ.pi fun _ ↦ Ici b) = rootTail d b := by
  rw [columnRootMeasure, withDensity_apply _ (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ici),
    Measure.restrict_pi_pi]
  rfl

def IsColumnChart {d : ℕ} (f : SL (d+1) → ColumnParameters d) : Prop :=
  Measurable f ∧ ∀ g p, HasColumnParameters g p ↔ f g = p

theorem columnRectangle_preimage {d : ℕ} {f : SL (d+1) → ColumnParameters d}
    (hf : IsColumnChart f) (b : ℝ) (S : Set (UpperEntry (d+1) → ℝ)) :
    columnRectangle d b S = f ⁻¹' ((univ.pi fun _ ↦ Ici b) ×ˢ S) := by
  ext g
  constructor
  · rintro ⟨k,u,a,hk,ha,hb,hu,hz,hS,hg⟩
    have h := (hf.2 g (fun i ↦ Real.log (a i.succ) - Real.log (a i.castSucc),
      fun i ↦ u i.val.1 i.val.2)).mp ⟨k,u,a,hk,ha,hu,hz,hg,rfl,rfl⟩
    change (f g).1 ∈ _ ∧ (f g).2 ∈ _
    rw [h]
    exact ⟨fun i _ ↦ hb i, hS⟩
  · rintro ⟨hb,hS⟩
    obtain ⟨k,u,a,hk,ha,hu,hz,hg,ht,hv⟩ := (hf.2 g _).mpr rfl
    exact ⟨k,u,a,hk,ha,fun i ↦ (congrFun ht i).symm ▸ hb i trivial,hu,hz,hv ▸ hS,hg⟩

/-- Evaluate the QR pushforward on a product of a root orthant and an upper-entry set. -/
theorem columnRectangleLaw_of_chart {d : ℕ} {f : SL (d+1) → ColumnParameters d}
    (hf : IsColumnChart f) (C : ℝ) (hμ : (groupHaar (d+1)).map f =
      ENNReal.ofReal C • (columnRootMeasure d).prod volume) : ColumnRectangleLaw d := by
  refine ⟨C, fun b S hS ↦ ?_⟩
  rw [columnRectangle_preimage hf, ← Measure.map_apply hf.1
    ((MeasurableSet.univ_pi fun _ ↦ measurableSet_Ici).prod hS), hμ,
    Measure.smul_apply, smul_eq_mul, Measure.prod_prod, columnRootMeasure_tail]
  ac_rfl

#print axioms columnRectangleLaw_of_chart
end SigabaNeo.Rogers

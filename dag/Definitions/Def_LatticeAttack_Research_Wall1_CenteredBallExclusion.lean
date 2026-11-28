import Definitions.Def_LatticeAttack_Research_Wall1_RawBallCount

set_option autoImplicit true

/-! # Centered integer balls by finite coordinate-cap exclusion

The excluded caps may overlap and include boundary points that are still centered.
Their union is used only as an upper bound for the removed integer points.
-/

noncomputable section
namespace SigabaNeo.Wall1.RawBallRounding
open Finset Real
open scoped Classical

/-- The full integer ball restricted to centered representatives modulo3329. -/
def centeredLifts (n : ℕ) (r : ℝ) : Finset (Fin n → ℤ) :=
  (closedLifts n r).filter fun z ↦ ∀ i, -1664 ≤ z i ∧ z i ≤ 1664

theorem mem_centeredLifts {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (z : Fin n → ℤ) :
    z ∈ centeredLifts n r ↔ energy z ≤ r^2 ∧ ∀ i, -1664 ≤ z i ∧ z i ≤ 1664 := by
  simp only [centeredLifts, mem_filter, mem_closedLifts hr]

/-- The two signed caps in every coordinate cover every noncentered point.
No disjointness of the caps is required, including in dimension zero. -/
theorem closedLifts_card_le_centered_add_caps (n : ℕ) (r : ℝ) :
    (closedLifts n r).card ≤ (centeredLifts n r).card +
      ∑ p : Fin n × Bool,
        ((closedLifts n r).filter fun z ↦ 1664 ≤ (if p.2 then z p.1 else -z p.1)).card := by
  let cap (p : Fin n × Bool) :=
    (closedLifts n r).filter fun z ↦ 1664 ≤ (if p.2 then z p.1 else -z p.1)
  have hcover : closedLifts n r ⊆ centeredLifts n r ∪ univ.biUnion cap := by
    intro z hz
    by_cases hc : ∀ i, -1664 ≤ z i ∧ z i ≤ 1664
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hz, hc⟩))
    · apply mem_union.mpr
      apply Or.inr
      obtain ⟨p, hp⟩ := not_forall.mp hc
      by_cases hneg : z p < -1664
      · exact mem_biUnion.mpr ⟨(p, false), mem_univ _,
          mem_filter.mpr ⟨hz, by simp only [Bool.false_eq_true, ite_false]; omega⟩⟩
      · exact mem_biUnion.mpr ⟨(p, true), mem_univ _,
          mem_filter.mpr ⟨hz, by simp only [ite_true]; omega⟩⟩
  exact (card_le_card hcover).trans
    ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))

/-- Subtracting the existing cap upper bounds gives a lower count for the actual
centered integer family. The estimate is valid for every dimension, including zero. -/
theorem centeredLifts_lower_from_full (n : ℕ) {r : ℝ} (hr : 1690 ≤ r) :
    ((closedLifts n r).card : ℝ) -
      4 * n * sqrt (r^2 - 1664^2 + n/4)^n * unitVolume n ≤
        (centeredLifts n r).card := by
  have hcover : ((closedLifts n r).card : ℝ) ≤ (centeredLifts n r).card +
      ∑ p : Fin n × Bool,
        (((closedLifts n r).filter fun z ↦
          1664 ≤ (if p.2 then z p.1 else -z p.1)).card : ℝ) := by
    exact_mod_cast closedLifts_card_le_centered_add_caps n r
  have hcaps :
      (∑ p : Fin n × Bool,
        (((closedLifts n r).filter fun z ↦
          1664 ≤ (if p.2 then z p.1 else -z p.1)).card : ℝ)) ≤
        4 * n * sqrt (r^2 - 1664^2 + n/4)^n * unitVolume n := by
    calc
      _ ≤ ∑ _p : Fin n × Bool,
          2 * sqrt (r^2 - 1664^2 + n/4)^n * unitVolume n :=
        sum_le_sum fun p _ ↦ cap_upper p.1 p.2 hr
      _ = _ := by simp; ring
  linarith

end SigabaNeo.Wall1.RawBallRounding

#print axioms SigabaNeo.Wall1.RawBallRounding.mem_centeredLifts
#print axioms SigabaNeo.Wall1.RawBallRounding.closedLifts_card_le_centered_add_caps
#print axioms SigabaNeo.Wall1.RawBallRounding.centeredLifts_lower_from_full

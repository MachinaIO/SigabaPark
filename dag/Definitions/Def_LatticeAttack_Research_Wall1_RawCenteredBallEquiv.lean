import Definitions.Def_LatticeAttack_Research_Wall1_CenteredPrefixOccupancy
import Definitions.Def_LatticeAttack_Research_Wall1_RawBallCount

set_option autoImplicit true

/-! The actual centered prefix candidates are exactly the coordinate-filtered integer ball. -/
noncomputable section
namespace SigabaNeo.Wall1.CenteredPrefixOccupancy
open RawBallRounding ControlledPlane
open scoped Classical

/-- Concatenation identifies every centered prefix candidate with its full integer vector. -/
theorem centeredBall_map_append {k : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    (centeredBall k R).map (Fin.appendEquiv (α := ℤ) 400 k).toEmbedding =
      (closedLifts (400+k) R).filter
        (fun z ↦ ∀ i, -1664 ≤ z i ∧ z i ≤ 1664) := by
  ext z
  rw [Finset.mem_map_equiv, mem_centeredBall, Finset.mem_filter, mem_closedLifts hR]
  change ((∀ i, -1664 ≤ z (Fin.castAdd k i) ∧ z (Fin.castAdd k i) ≤ 1664) ∧
      (∀ i, -1664 ≤ z (Fin.natAdd 400 i) ∧ z (Fin.natAdd 400 i) ≤ 1664) ∧
      (∑ i : Fin 400, (z (Fin.castAdd k i) : ℝ)^2) +
        (∑ i : Fin k, (z (Fin.natAdd 400 i) : ℝ)^2) ≤ R^2) ↔
    (∑ i, (z i : ℝ)^2) ≤ R^2 ∧ (∀ i, -1664 ≤ z i ∧ z i ≤ 1664)
  rw [Fin.sum_univ_add, Fin.forall_fin_add]
  tauto

/-- Cardinalities agree without losing the origin or any boundary points. -/
theorem centeredBall_card_append {k : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    (centeredBall k R).card =
      ((closedLifts (400+k) R).filter
        (fun z ↦ ∀ i, -1664 ≤ z i ∧ z i ≤ 1664)).card := by
  rw [← centeredBall_map_append hR, Finset.card_map]

/-- The concrete 119-input candidate count is the centered 519-dimensional ball count. -/
theorem slackBall_card_append {R : ℝ} (hR : 0 ≤ R) :
    (centeredBall 119 R).card =
      ((closedLifts 519 R).filter
        (fun z ↦ ∀ i, -1664 ≤ z i ∧ z i ≤ 1664)).card :=
  centeredBall_card_append hR

end SigabaNeo.Wall1.CenteredPrefixOccupancy
#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.centeredBall_map_append
#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.centeredBall_card_append
#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.slackBall_card_append

module

public import Definitions.Def_LatticeAttack_Research_Wall1_CBDQuadratic
public import Definitions.Def_LatticeAttack_Research_Wall1_UniquenessCriterion
public import Mathlib.Analysis.InnerProductSpace.PiL2
import all Definitions.Def_LatticeAttack_Research_Wall1_CBDQuadratic
import all Definitions.Def_LatticeAttack_Research_Wall1_CBDTail
import Mathlib.Tactic

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1

open SampleDeletion CBDTail CBDQuadratic Matrix
open scoped BigOperators

variable {N : ℕ}

/-- Project the centered CBD sample into the horizontal Euclidean space. -/
noncomputable def projectedCBD (Q : Matrix (Fin N) (Fin N) ℝ) (w : Fin N → Digit 3) :
    EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (Q.mulVec fun i ↦ (centered (w i) : ℝ))

theorem projectedCBD_norm_sq (Q : Matrix (Fin N) (Fin N) ℝ) (hs : Q.transpose = Q)
    (hp : Q * Q = Q) (w : Fin N → Digit 3) : ‖projectedCBD Q w‖ ^ 2 = quadratic Q w := by
  let x : Fin N → ℝ := fun i ↦ centered (w i)
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [sq]
  change dotProduct (Q.mulVec x) (Q.mulVec x) = _
  rw [← Matrix.dotProduct_transpose_mulVec Q x (Q.mulVec x), hs, Matrix.mulVec_mulVec, hp]
  simp [dotProduct, Matrix.mulVec, quadratic, x, Finset.mul_sum, mul_left_comm]

/-- The all-heights event for the closed ball through the two signed plants. -/
def allHeightsUnique (H : AddSubgroup (EuclideanSpace ℝ (Fin N)))
    (y : EuclideanSpace ℝ (Fin N)) : Prop :=
  ∀ h ∈ H, ∀ k : ℤ, ‖h + k • y‖ ^ 2 + (k : ℝ) ^ 2 ≤ ‖y‖ ^ 2 + 1 ↔
    h = 0 ∧ (k = 0 ∨ k = 1 ∨ k = -1)

open Classical in
/-- A nonzero horizontal vector at or below the floor caps uniqueness mass at 99%. -/
theorem heightZeroFloor (Q : Matrix (Fin N) (Fin N) ℝ) (hs : Q.transpose = Q)
    (hp : Q * Q = Q) (hd : 1 ≤ Q.trace) (H : AddSubgroup (EuclideanSpace ℝ (Fin N)))
    (short : ∃ h ∈ H, h ≠ 0 ∧ ‖h‖ ^ 2 ≤
      1 + (3/2) * Q.trace - Real.sqrt ((9/2) * Q.trace / 99)) :
    (∑ w with allHeightsUnique H (projectedCBD Q w), jointWeight w) ≤ 99/100 := by
  classical
  obtain ⟨h, hh, hn, hshort⟩ := short
  let a := Real.sqrt ((9/2) * Q.trace / 99)
  have ht : 0 < Q.trace := by linarith
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have ha₂ : a ^ 2 = (9/2) * Q.trace / 99 := Real.sq_sqrt (by positivity)
  have hw (w : Fin N → Digit 3) : 0 ≤ jointWeight w := by
    unfold jointWeight weight
    positivity
  apply le_trans _ ((quadratic_cantelli Q a ha).trans ?_)
  · apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun w _ _ ↦ hw w)
    intro w hwmem
    obtain ⟨hmem, hu⟩ := Finset.mem_filter.mp hwmem
    apply Finset.mem_filter.mpr ⟨hmem, ?_⟩
    have lt := ((allHeightsUniquenessCriterion H _).mp hu).1 h hh hn
    rw [projectedCBD_norm_sq Q hs hp] at lt
    change ‖h‖ ^ 2 ≤ 1 + (3/2) * Q.trace - a at hshort
    linarith
  · have hv := projection_variance_le Q hs hp
    have hv₀ : 0 ≤ ∑ w, jointWeight w * (quadratic Q w - (3/2)*Q.trace)^2 :=
      Finset.sum_nonneg fun w _ ↦ mul_nonneg (hw w) (sq_nonneg _)
    apply (div_le_iff₀ (add_pos_of_nonneg_of_pos hv₀ (sq_pos_of_pos ha))).2
    linarith

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.heightZeroFloor

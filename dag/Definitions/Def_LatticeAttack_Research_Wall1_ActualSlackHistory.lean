import Definitions.Def_LatticeAttack_Research_Wall1_SlackDeterminantRadius

set_option autoImplicit true

/-! # The determinant-gated bound on the actual restart history

No determinant or winner functions are supplied by the caller. The radius uses
the actual retained determinant after the current append/freeze step. The raw
first-moment sum remains an explicit, unevaluated right-hand side.
-/

noncomputable section
namespace SigabaNeo.Wall1.CenteredPrefixOccupancy
open Finset ControlledPlane TerminalProjection TerminalProjection.Restart506
open RawPrefixOccupancy CosetOccupancy LongWinner
open scoped Classical

def retainedDeterminant (A : Sample) (j : ℕ) : ℝ :=
  ZLattice.covolume (retained (history A) j).M

/-- Closed-ball radius after the current freeze, retaining the squared reserve two. -/
def actualSlackRadius (A : Sample) (j : ℕ) : ℝ :=
  Real.sqrt ((121 / 100) * terminalScale (retainedDeterminant A (j+1)) ^ 2 - 2)

private theorem terminalScale_sq {D : ℝ} (hD : 0 ≤ D) :
    terminalScale D ^ 2 = (D / terminalBallVolume) ^ (1 / (253 : ℝ)) := by
  have hv : 0 < terminalBallVolume := by rw [terminalBallVolume_eq]; positivity
  unfold terminalScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hD hv.le)]
  norm_num

/-- The operational determinant update identifies the numerical radius exactly. -/
theorem actualSlackRadius_eq (A : Sample) (j : ℕ) (hj : j < 406) :
    actualSlackRadius A j = determinantRadius (retainedDeterminant A j)
      (length (path (history A)) j) := by
  have hp := det_pos (path (history A)) (j+1) (by omega)
  have he := (path_data (path (history A)) j hj).2.2.1
  change Real.sqrt ((121 / 100) * terminalScale ((path (history A)).det (j+1)) ^ 2 - 2) = _
  rw [terminalScale_sq hp.le, he]
  rfl

attribute [local instance 10000] historyExistsDecidable

section
-- Avoid the known naming-linter recursion on concrete finite-matrix expressions.
set_option linter.constructorNameAsVariable false

/-- All matrices having at least one gated empty-coset exit in draws15..404. -/
def gatedExitSet (gate : Fin 390 → Sample → Prop) (radius : Fin 390 → Sample → ℝ) : Finset Sample :=
  univ.filter fun A ↦ ∃ i : Fin 390, gate i A ∧
    7 * Fintype.card (StateMark A (entry i)) ≤
      25 * emptyCount (occupied A (entry i) (radius i A))

/-- The named set keeps the exact existential event, with no relaxed predicate. -/
theorem mem_gatedExitSet (gate : Fin 390 → Sample → Prop)
    (radius : Fin 390 → Sample → ℝ) (A : Sample) :
    A ∈ gatedExitSet gate radius ↔ ∃ i : Fin 390, gate i A ∧
      7 * Fintype.card (StateMark A (entry i)) ≤
        25 * emptyCount (occupied A (entry i) (radius i A)) := by
  simp only [gatedExitSet, mem_filter, mem_univ, true_and]

private theorem gated_history (gate : Fin 390 → Sample → Prop)
    (radius : Fin 390 → Sample → ℝ)
    (hg : ∀ i A, gate i A → slackRadius ≤ radius i A) :
    7 * Fintype.card Column *
      (gatedExitSet gate radius).card ≤
    25 * ∑ A, emptyCount
      (rawCount (by decide : 119 ≤ 512) (centeredBall 119 slackRadius) A) := by
  have hsubset :
      (univ.filter fun A ↦ ∃ i : Fin 390, gate i A ∧
        7 * Fintype.card (StateMark A (entry i)) ≤
          25 * emptyCount (occupied A (entry i) (radius i A))) ⊆
      (univ.filter fun A ↦ ∃ i : Fin 390,
        slackRadius ≤ radius i A ∧
        7 * Fintype.card (StateMark A (entry i)) ≤
          25 * emptyCount (occupied A (entry i) (radius i A))) := by
    intro A hA
    simp only [mem_filter, mem_univ, true_and] at hA ⊢
    obtain ⟨i, hi, he⟩ := hA
    exact ⟨i, hg i A hi, he⟩
  exact (Nat.mul_le_mul_left (7 * Fintype.card Column) (card_le_card hsubset)).trans
    (slack_history_exit_first_moment radius)

private theorem actual_gate (i : Fin 390) (A : Sample)
    (hD : 12 * (3329 : ℝ)^386 ≤ retainedDeterminant A (entry i)) :
    slackRadius ≤ actualSlackRadius A (entry i) := by
  have hj : entry i < 406 := by dsimp [entry]; omega
  rw [actualSlackRadius_eq A (entry i) hj]
  exact slackRadius_le_determinantRadius _ _ hD
    (path_data (path (history A)) (entry i) hj).1
    (path_data (path (history A)) (entry i) hj).2.1

/-- Actual-history exits on draws15..404 under the determinant gate. All geometry
and divisor hypotheses are discharged; only the raw numerical sum remains. -/
theorem actual_slack_history_exit_first_moment :
    7 * Fintype.card Column *
      (gatedExitSet
        (fun i A ↦ 12 * (3329 : ℝ)^386 ≤ retainedDeterminant A (entry i))
        (fun i A ↦ actualSlackRadius A (entry i))).card ≤
    25 * ∑ A, emptyCount
      (rawCount (by decide : 119 ≤ 512) (centeredBall 119 slackRadius) A) := by
  exact gated_history
    (fun i A ↦ 12 * (3329 : ℝ)^386 ≤ retainedDeterminant A (entry i))
    (fun i A ↦ actualSlackRadius A (entry i)) actual_gate

end
end SigabaNeo.Wall1.CenteredPrefixOccupancy

#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.actualSlackRadius_eq
#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.mem_gatedExitSet
#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.actual_slack_history_exit_first_moment

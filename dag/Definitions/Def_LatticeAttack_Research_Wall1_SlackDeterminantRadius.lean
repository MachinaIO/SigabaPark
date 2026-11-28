import Definitions.Def_LatticeAttack_Research_Wall1_CenteredPrefixOccupancy
import Definitions.Def_LatticeAttack_Research_Wall1_TerminalScale506

set_option autoImplicit true

/-! # Determinant gate for the exact integer slack ball

This certifies the radius comparison using the actual width-506 ball volume.
The history law and raw numerical first moment are not assumed or proved here.
-/

noncomputable section
namespace SigabaNeo.Wall1.CenteredPrefixOccupancy
open TerminalProjection

/-- The post-quotient radius with squared witness reserve two. -/
def determinantRadius (D s : ℝ) : ℝ :=
  Real.sqrt ((121 / 100) * ((D / s) / terminalBallVolume) ^ (1 / (253 : ℝ)) - 2)

private theorem cutoff_volume_bound :
    (8415831 * 100 / 121 : ℝ)^253 * terminalBallVolume ≤ 12 * (3329 : ℝ)^385 := by
  let p : ℚ := 3.14159265358979323847
  have hp : Real.pi ≤ (p : ℝ) := by simpa [p] using Real.pi_lt_d20.le
  rw [terminalBallVolume_eq, ← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).2
  calc
    _ ≤ (8415831 * 100 / 121 : ℝ)^253 * (p : ℝ)^253 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hp _) (by positivity)
    _ ≤ _ := by
      have h := (Rat.cast_le (K := ℝ)).2
        (show (8415831 * 100 / 121 : ℚ)^253 * p^253 ≤
          12 * (3329 : ℚ)^385 * (Nat.factorial 253 : ℚ) by decide +kernel)
      push_cast at h
      exact h

/-- The exact integer candidate ball fits whenever the retained determinant has slack12.
Only positivity and the period upper bound on the actual divisor are needed. -/
theorem slackRadius_le_determinantRadius (D s : ℝ)
    (hD : 12 * (3329 : ℝ)^386 ≤ D) (hs : 0 < s) (hsq : s ≤ 3329) :
    slackRadius ≤ determinantRadius D s := by
  have hv : 0 < terminalBallVolume := by rw [terminalBallVolume_eq]; positivity
  have hDs : 12 * (3329 : ℝ)^385 ≤ D / s := by
    apply (le_div_iff₀ hs).2
    calc
      _ ≤ (12 * (3329 : ℝ)^385) * 3329 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ D := by
        rw [show (3329 : ℝ)^386 = (3329 : ℝ)^385 * 3329 from pow_succ _ _] at hD
        simpa only [mul_assoc] using hD
  have hroot : (8415831 * 100 / 121 : ℝ) ≤
      ((D / s) / terminalBallVolume) ^ (1 / (253 : ℝ)) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num)
      (div_nonneg (le_trans (by positivity) hDs) hv.le) (by norm_num)).2
    rw [show (253 : ℝ) = (253 : ℕ) by norm_num, Real.rpow_natCast]
    exact (le_div_iff₀ hv).2 (cutoff_volume_bound.trans hDs)
  unfold slackRadius determinantRadius
  apply Real.sqrt_le_sqrt
  linarith

open Finset ControlledPlane RawPrefixOccupancy CosetOccupancy
open scoped Classical

attribute [local instance 10000] historyExistsDecidable

section
-- This naming linter exceeds its recursion limit on the concrete finite-matrix
-- expression. Kernel checking and the axiom audit remain enabled.
set_option linter.constructorNameAsVariable false
/-- Replace the abstract radius gate by the concrete determinant gate, retaining
the original matrix law and the common raw first moment without a horizon factor.
Applications must identify D and s with their actual retained determinant and divisor. -/
theorem determinant_gate_history_exit_first_moment
    (D s : Fin 390 → Sample → ℝ)
    (hs : ∀ i A, 0 < s i A) (hsq : ∀ i A, s i A ≤ 3329) :
    7 * Fintype.card Column *
      (univ.filter fun A ↦ ∃ i, 12 * (3329 : ℝ)^386 ≤ D i A ∧
        7 * Fintype.card (StateMark A (entry i)) ≤
          25 * emptyCount (occupied A (entry i) (determinantRadius (D i A) (s i A)))).card ≤
    25 * ∑ A, emptyCount
      (rawCount (by decide : 119 ≤ 512) (centeredBall 119 slackRadius) A) := by
  have hsubset :
      (univ.filter fun A ↦ ∃ i, 12 * (3329 : ℝ)^386 ≤ D i A ∧
        7 * Fintype.card (StateMark A (entry i)) ≤
          25 * emptyCount (occupied A (entry i) (determinantRadius (D i A) (s i A)))) ⊆
      (univ.filter fun A ↦ ∃ i, slackRadius ≤ determinantRadius (D i A) (s i A) ∧
        7 * Fintype.card (StateMark A (entry i)) ≤
          25 * emptyCount (occupied A (entry i) (determinantRadius (D i A) (s i A)))) := by
    intro A hA
    simp only [mem_filter, mem_univ, true_and] at hA ⊢
    obtain ⟨i, hD, hexit⟩ := hA
    exact ⟨i,
      slackRadius_le_determinantRadius _ _ hD (hs i A) (hsq i A), hexit⟩
  exact (Nat.mul_le_mul_left _ (card_le_card hsubset)).trans
    (slack_history_exit_first_moment (fun i A ↦ determinantRadius (D i A) (s i A)))

end

end SigabaNeo.Wall1.CenteredPrefixOccupancy

#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.slackRadius_le_determinantRadius
#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.determinant_gate_history_exit_first_moment

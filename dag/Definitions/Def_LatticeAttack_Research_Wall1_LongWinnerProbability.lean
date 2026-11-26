import Definitions.Def_LatticeAttack_Research_Wall1_AdaptedBinomialTail
import Definitions.Def_LatticeAttack_Research_Wall1_LongWinnerCrossing

set_option autoImplicit true

/-! Part 216 on the uniform finite design law. Draw numbers are one-based in the note. -/

noncomputable section
namespace SigabaNeo.Wall1.LongWinner
open TerminalProjection TerminalProjection.Restart506 Blichfeldt ControlledPlane Finset
open DualExit QaryMembership AdaptedBinomial
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- Long-winner indicator on a sampled graph. -/
def exceptional (i : ℕ) (A : Sample) : Prop := Long (path (history A)) i

/-- Incoming draws 396–406 on which the scale drops strictly below the threshold. -/
def crosses (A : Sample) : Prop :=
  ∃ i ∈ Icc 395 405, terminalScale ((path (history A)).det i) < 34.807

private def weight (_ : Sample) : ℝ := (Fintype.card Sample : ℝ)⁻¹

private theorem mass_eq (A : Sample → Prop) :
    AdaptedBinomial.mass weight A = probability A := by
  unfold AdaptedBinomial.mass probability designs
  rw [← sum_filter]
  simp only [weight, sum_const, nsmul_eq_mul, div_eq_mul_inv]

private theorem count_eq (A : Sample) (n : ℕ) :
    count exceptional n A = longCount (path (history A)) n := by
  induction n with
  | zero => simp [count,longCount]
  | succ n ih =>
    simp [count,ih,longCount,range_add_one,filter_insert,exceptional]
    split_ifs <;> simp_all

/-- A single upper tail covers the union over the eleven incoming windows. -/
theorem crossing_probability (ceiling : ∀ i < 405, ∀ B : Sample → Prop,
    PrefixTest exceptional i B → probability (fun A ↦ B A ∧ exceptional i A) ≤
      0.126 * probability B) :
    probability crosses < 2.5881467826 / (10:ℝ)^11 := by
  have h := ceiling_of_history weight exceptional 405 0.126 (by simpa only [mass_eq] using ceiling)
  have H := dominated (μ := weight) (fun _ ↦ by unfold weight; positivity)
    (by
      simp only [weight, sum_const, card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_pos.ne'))
    exceptional (by norm_num : (0:ℝ) ≤ 0.126) (by norm_num) 405 h 100
  rw [mass_eq] at H
  apply lt_of_le_of_lt ((probability_mono (Q := fun A ↦ 100 ≤ count exceptional 405 A) ?_).trans H)
    tail_405_bracket.2
  rintro A ⟨i, hi, bad⟩
  rw [count_eq]
  by_contra! few
  exact (scale_of_at_most_99 _ (by omega) i (by have := (mem_Icc.mp hi).1; omega)
    (mem_Icc.mp hi).2).not_gt bad

end SigabaNeo.Wall1.LongWinner

#print axioms SigabaNeo.Wall1.LongWinner.crossing_probability

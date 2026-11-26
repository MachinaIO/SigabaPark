import Definitions.Def_LatticeAttack_Attacks_Bkw_BinaryPair
import Definitions.Def_LatticeAttack_Attacks_Bkw_Majority
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit true

/-!
# Binary one-stage BKW with a majority vote, end to end

One vote draws two fresh rows: uniform blocks `b, c`, fair last coefficients `x, y`, independent
Bernoulli(`p`) errors `e, f`, and a fair fallback bit. It runs `BinaryPair.run`. The law of one vote
is the finite product law `voteLaw`, and its success probability is exactly
`1/2 + (1−2p)²/(4|B|)` (`voteLaw_success`, from `BinaryPair.end_to_end`). Taking the majority of
`N` independent votes (`binaryMajority`) recovers the secret bit except with probability
`exp(−2Nγ²)`, `γ = (1−2p)²/(4|B|)`, using at most `6N` charged operations (`tally_cost`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SigabaNeo.Lattices.Attacks.Bkw.BinaryPair

variable {B : Type} [DecidableEq B] [Fintype B] [Nonempty B]

/-- The randomness of one vote: blocks, last coefficients, errors, fallback coin. -/
abbrev Vote (B : Type) := B × B × Bool × Bool × Bool × Bool × Bool

/-- Probability weight of a Bernoulli(`p`) bit. -/
noncomputable def bw (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- The weight of one vote's randomness. -/
noncomputable def voteWeight (p : ℝ) (ω : Vote B) : ℝ :=
  (1 / (Fintype.card B : ℝ)) * (1 / (Fintype.card B : ℝ)) * bw (1/2) ω.2.2.1 *
    bw (1/2) ω.2.2.2.1 * bw p ω.2.2.2.2.1 * bw p ω.2.2.2.2.2.1 * bw (1/2) ω.2.2.2.2.2.2

/-- The vote's outcome is correct. -/
abbrev correct (t : B → Bool) (s : Bool) (ω : Vote B) : Prop :=
  ((run (row t s ω.1 ω.2.2.1 ω.2.2.2.2.1) (row t s ω.2.1 ω.2.2.2.1 ω.2.2.2.2.2.1)
    ω.2.2.2.2.2.2).run 0).1 = s

theorem bern_eq (p : ℝ) (f : Bool → ℝ) : bern p f = ∑ b, bw p b * f b := by
  simp [bern, bw]; ring

/-- Summing the weights of the correct outcomes gives the one-vote success probability. -/
theorem weight_sum_correct (t : B → Bool) (s : Bool) (p : ℝ) :
    ∑ ω : Vote B, (if correct t s ω then voteWeight p ω else 0) = success t s p := by
  classical
  simp only [success, fixedSuccess, bern_eq, voteWeight, correct, Fintype.sum_prod_type,
    Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  refine Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun f _ ↦ ?_
  refine Finset.sum_congr rfl fun coin _ ↦ ?_
  split_ifs <;> field_simp <;> ring

theorem bw_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (b : Bool) : 0 ≤ bw p b := by
  cases b <;> simp [bw] <;> linarith

theorem voteWeight_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (ω : Vote B) :
    0 ≤ voteWeight p ω := by
  have h2 := bw_nonneg (p := 1/2) (by norm_num) (by norm_num)
  have hp := bw_nonneg h0 h1
  have hc : 0 ≤ 1 / (Fintype.card B : ℝ) := by positivity
  unfold voteWeight
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc hc) (h2 _))
    (h2 _)) (hp _)) (hp _)) (h2 _)

theorem voteWeight_sum (p : ℝ) : ∑ ω : Vote B, voteWeight p ω = 1 := by
  have hc : (Fintype.card B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [voteWeight, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
  simp [bw, Fintype.sum_bool, Finset.sum_const, Finset.card_univ]
  field_simp

/-- The law of one vote's randomness. -/
noncomputable def votePMF {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : PMF (Vote B) :=
  PMF.ofFintype (fun ω ↦ ENNReal.ofReal (voteWeight p ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ ↦ voteWeight_nonneg h0 h1 ω), voteWeight_sum,
      ENNReal.ofReal_one])

variable [MeasurableSpace B] [MeasurableSingletonClass B]

theorem votePMF_correct {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (t : B → Bool) (s : Bool) :
    (votePMF h0 h1).toMeasure.real {ω | correct t s ω} = success t s p := by
  classical
  rw [measureReal_def, PMF.toMeasure_apply_fintype, ← weight_sum_correct t s p]
  rw [← ENNReal.toReal_ofReal (Finset.sum_nonneg fun ω _ ↦ by
    split_ifs
    · exact voteWeight_nonneg h0 h1 ω
    · exact le_refl 0)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun ω _ ↦ by
    split_ifs
    · exact voteWeight_nonneg h0 h1 ω
    · exact le_refl 0)]
  congr 1
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  simp only [Set.indicator, Set.mem_setOf_eq, votePMF, PMF.ofFintype_apply]
  split_ifs <;> simp_all

/-- **Binary one-stage BKW with a majority vote.** With `N` independent votes, each drawing two
fresh rows, the strict majority equals the secret bit except with probability
`exp(−2Nγ²)`, `γ = (1−2p)²/(4|B|)`; each vote costs at most 5 charged operations. -/
theorem binaryMajority {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (t : B → Bool) (s : Bool) (N : ℕ) :
    let γ := (1 - 2 * p) ^ 2 / (4 * Fintype.card B)
    1 - Real.exp (-2 * N * γ ^ 2) ≤
      (Measure.pi (fun _ : Fin N ↦ (votePMF h0 h1).toMeasure)).real
        {x | N < 2 * ∑ i : Fin N, ({ω | correct t s ω}.indicator (fun _ ↦ 1 : Vote B → ℕ) (x i))} ∧
    ∀ (u v : Row B) (coin : Bool), ((run u v coin).run 0).2 ≤ 5 := by
  intro γ
  refine ⟨SigabaNeo.Probability.iid_majority_count _ _ (Set.toFinite _).measurableSet (by positivity) ?_ N,
    (end_to_end t s ⟨p, h0, h1⟩).2⟩
  rw [votePMF_correct h0 h1 t s, (end_to_end t s ⟨p, h0, h1⟩).1]

end SigabaNeo.Lattices.Attacks.Bkw.BinaryPair

#print axioms SigabaNeo.Lattices.Attacks.Bkw.BinaryPair.binaryMajority

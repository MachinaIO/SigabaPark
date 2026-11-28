import Definitions.Def_LatticeAttack_Research_Wall1_RawPrefixMean

set_option autoImplicit true

/-! Exact ordered-pair representation of the raw second factorial moment. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset FactorialMomentTransfer ControlledPlane TerminalProjection


/-- Distinct candidates with the same syndrome, counted as ordered pairs. -/
def collisionPairs {α β : Type*} [DecidableEq α] [DecidableEq β] (T : Finset α) (f : α → β) : Finset (α × α) :=
  T.offDiag.filter fun p ↦ f p.1 = f p.2

theorem sum_fiber_descFactorial_two {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (T : Finset α) (f : α → β) :
    (∑ c, ((T.filter fun z ↦ f z = c).card).descFactorial 2) =
      (collisionPairs T f).card := by
  have he (c : β) : (T.filter fun z ↦ f z = c).offDiag =
      (collisionPairs T f).filter (fun p ↦ f p.1 = c) := by
    ext p
    simp only [mem_offDiag, mem_filter, collisionPairs]
    aesop
  have hc (c : β) : ((T.filter fun z ↦ f z = c).card).descFactorial 2 =
      ((collisionPairs T f).filter (fun p ↦ f p.1 = c)).card := by
    rw [← he, offDiag_card, Nat.descFactorial_succ, Nat.descFactorial_one]
    rw [Nat.sub_mul, Nat.one_mul]
  simp_rw [hc]
  have h := sum_card_fiberwise_eq_card_filter (collisionPairs T f) univ (fun p ↦ f p.1)
  simpa only [mem_univ, filter_true] using h

/-- Exchange matrix averaging and pair counting before applying fixed-pair probabilities. -/
theorem sum_collisionPairs_card {Ω α β : Type*} [Fintype Ω]
    [DecidableEq α] [DecidableEq β] (T : Finset α) (f : Ω → α → β) :
    (∑ A, (collisionPairs T (f A)).card) =
      ∑ p ∈ T.offDiag, (univ.filter fun A ↦ f A p.1 = f A p.2).card := by
  simp only [collisionPairs, card_filter]
  exact sum_comm

/-- A deterministic matrix identity; no independence assumption is used. -/
theorem raw_second_factorial_sum {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (A : Sample) :
    (∑ c, (rawCount hk T A c).descFactorial 2) =
      (collisionPairs T (rawSyndrome hk A)).card := by
  simp_rw [rawCount_eq_fiber]
  exact sum_fiber_descFactorial_two T (rawSyndrome hk A)

/-- Averaging the exact collision count gives the actual second factorial moment. -/
theorem raw_second_factorial_average {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k)) :
    factorialAverage (rawCount hk T) 2 =
      (∑ A, ((collisionPairs T (rawSyndrome hk A)).card : ℝ)) /
        ((Fintype.card Sample : ℝ) * Fintype.card Column) := by
  unfold factorialAverage
  apply congrArg (fun v : ℝ ↦ v / ((Fintype.card Sample : ℝ) * Fintype.card Column))
  apply sum_congr rfl
  intro A _
  exact_mod_cast raw_second_factorial_sum hk T A

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_second_factorial_average

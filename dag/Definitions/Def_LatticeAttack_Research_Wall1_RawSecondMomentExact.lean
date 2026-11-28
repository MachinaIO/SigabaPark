import Definitions.Def_LatticeAttack_Research_Wall1_RawSecondMoment
import Definitions.Def_LatticeAttack_Research_Wall1_RawPairCollision
import Definitions.Def_LatticeAttack_Research_Wall1_CandidateInputPairs

set_option autoImplicit true

/-! Exact second factorial moment for a fixed centered candidate family. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane TerminalProjection FactorialMomentTransfer CandidateInputPairs

/-- Matrix averaging of syndrome collisions only retains pairs with distinct inputs. -/
theorem raw_collision_average {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (hout : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664)
    (hin : ∀ z ∈ T, ∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664) :
    (∑ A, ((collisionPairs T (rawSyndrome hk A)).card : ℝ)) /
      Fintype.card Sample =
      ((((T ×ˢ T).filter fun p ↦ p.1.2 ≠ p.2.2).card : ℝ)) / (3329 : ℝ)^400 := by
  rw [← Nat.cast_sum, sum_collisionPairs_card, Nat.cast_sum, sum_div]
  have hp (p : Candidate k × Candidate k) (hmem : p ∈ T.offDiag) :
      ((univ.filter fun A : Sample ↦ rawSyndrome hk A p.1 = rawSyndrome hk A p.2).card : ℝ) /
        Fintype.card Sample = if p.1.2 ≠ p.2.2 then 1/(3329 : ℝ)^400 else 0 := by
    obtain ⟨hz, hw, hne⟩ := mem_offDiag.mp hmem
    by_cases hinput : p.1.2 = p.2.2
    · rw [if_neg (not_not.mpr hinput)]
      have houtput : p.1.1 ≠ p.2.1 := fun h ↦ hne (Prod.ext h hinput)
      have he : (univ.filter fun A : Sample ↦
          rawSyndrome hk A p.1 = rawSyndrome hk A p.2) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro A _
        exact rawSyndrome_ne_of_same_input hk A p.1 p.2
          (hout _ hz) (hout _ hw) hinput houtput
      rw [he, card_empty, Nat.cast_zero, zero_div]
    · rw [if_pos hinput]
      exact rawSyndrome_collision_probability hk p.1 p.2 (hin _ hz) (hin _ hw) hinput
  rw [sum_congr rfl hp, ← sum_filter]
  have he : (T.offDiag.filter fun p ↦ p.1.2 ≠ p.2.2) =
      ((T ×ˢ T).filter fun p ↦ p.1.2 ≠ p.2.2) := by
    ext p
    simp only [mem_filter, mem_offDiag, mem_product]
    constructor
    · rintro ⟨⟨hz,hw,_⟩, h⟩
      exact ⟨⟨hz,hw⟩,h⟩
    · rintro ⟨⟨hz,hw⟩, h⟩
      exact ⟨⟨hz,hw,fun e ↦ h (congrArg (fun z : Candidate k ↦ z.2) e)⟩,h⟩
  rw [he, sum_const, nsmul_eq_mul, mul_one_div]

/-- Exact second factorial moment under the original independent uniform matrix/label law. -/
theorem raw_second_factorial_exact {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (hout : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664)
    (hin : ∀ z ∈ T, ∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664) :
    factorialAverage (rawCount hk T) 2 =
      ((T.card : ℝ)^2 - (inputSquareSum T Prod.snd : ℝ)) / (3329 : ℝ)^800 := by
  rw [raw_second_factorial_average, ← div_div, raw_collision_average hk T hout hin]
  have hc : Fintype.card Column = 3329^400 := by simp [Column]
  rw [hc, Nat.cast_pow, Nat.cast_ofNat, div_div, ← pow_add]
  rw [different_input_pairs_card, Nat.cast_sub (inputSquareSum_le_card_sq T Prod.snd), Nat.cast_pow]

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_collision_average
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_second_factorial_exact

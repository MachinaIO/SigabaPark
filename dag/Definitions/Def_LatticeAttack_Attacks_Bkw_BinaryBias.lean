module

public import Definitions.Def_LatticeAttack_Attacks_Bkw_BinaryPair
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.Attacks.Bkw.BinaryPair

variable {B : Type} [DecidableEq B] [Fintype B] [Nonempty B]

/-- A fresh pair gives a strict advantage precisely away from fair noise. -/
theorem advantage_iff (t : B → Bool) (s : Bool) (p : Set.Icc (0 : ℝ) 1) :
    1 / 2 < success t s p ↔ (p : ℝ) ≠ 1 / 2 := by
  rw [(end_to_end t s p).1]
  constructor
  · intro h he
    norm_num [he] at h
  · intro h
    have hn : 1 - 2 * (p : ℝ) ≠ 0 := by
      intro hz
      apply h
      linarith
    have hc : (0 : ℝ) < Fintype.card B := Nat.cast_pos.mpr Fintype.card_pos
    exact lt_add_of_pos_right _ (div_pos (sq_pos_of_ne_zero hn) (by positivity))

/-- At fair noise Lean's total division admits one trial for every constant in the
proposed threshold, although a one-vote majority succeeds with probability one half. -/
theorem fair_noise_counterexample (t : B → Bool) (s : Bool) (C : ℝ) :
    C * (Fintype.card B : ℝ)^2 * Real.log 4 / (1 - 2 * (1/2 : ℝ))^4 ≤ 1 ∧
    success t s (1/2) < 1 - 1/4 := by
  constructor
  · norm_num
  · rw [(end_to_end t s ⟨1/2, by constructor <;> norm_num⟩).1]
    norm_num

#print axioms advantage_iff
#print axioms fair_noise_counterexample

end SigabaNeo.Lattices.Attacks.Bkw.BinaryPair

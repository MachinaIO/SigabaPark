import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

set_option autoImplicit true

/-! # Falling-factorial product linearization through degree12

The finite index range is checked by polynomial identities for arbitrary real
arguments, not by sampling arguments or trusting a generated numerical table.
-/

namespace SigabaNeo.Wall1.CharlierVoidKernel
open Finset Polynomial

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem desc_product_bounded (i j : ℕ) (hi : i ≤ 12) (hj : j ≤ 12) (x : ℝ) :
    (descPochhammer ℝ i).eval x * (descPochhammer ℝ j).eval x =
    ∑ l ∈ range (min i j + 1),
      ((Nat.choose i l * Nat.choose j l * l.factorial : ℕ) : ℝ) *
        (descPochhammer ℝ (i + j - l)).eval x := by
  interval_cases i <;> interval_cases j <;>
    norm_num [Nat.choose, sum_range_succ, descPochhammer_succ_right, descPochhammer_zero,
    eval_mul, eval_sub, eval_X, eval_natCast] <;> ring

end SigabaNeo.Wall1.CharlierVoidKernel

#print axioms SigabaNeo.Wall1.CharlierVoidKernel.desc_product_bounded

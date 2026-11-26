module

public import Mathlib

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1Rej

/-- Expected continuation value after uniform proposals, with a retry on rejection. -/
theorem retryValue (a b g x : ℚ) (ha : 0 < a) (hb : 0 < b)
    (h : x = g / b + (1 - a / b) * x) : x = g / a := by
  field_simp [ne_of_gt hb] at h
  apply (eq_div_iff (ne_of_gt ha)).2
  linarith only [h]

/-- Likelihood of selecting the first axis among shortest sign classes of a binary row.
False denotes the zero syndrome. -/
def firstAxis (u v : Bool) : ℚ :=
  if u then 0 else if v then 1 else 1 / 2

/-- Given the first axis, the probability that the remaining column vanishes is 1/3. -/
theorem selectedZero :
    firstAxis false false /
      (firstAxis false false + firstAxis false true +
       firstAxis true false + firstAxis true true) = 1 / 3 := by
  norm_num [firstAxis]

/-- Mixing fresh uniform columns in quotients of a single binary syndrome cannot match it.
The trivial quotient has mixture weight t. -/
theorem noFreshMixture (t : ℚ) (ht : 0 ≤ t) :
    t + (1 - t) / 2 ≠ 1 / 3 := by linarith

#print axioms retryValue
#print axioms selectedZero
#print axioms noFreshMixture

end SigabaNeo.Wall1Rej

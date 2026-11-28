import Mathlib.Tactic

namespace SyndromePhaseGuard

/-- The four independent legal character coordinates encoded in radix four. -/
def digit (x j : Nat) : Nat := x / 4 ^ j % 4

/-- An integer weight relative to the uniform 256-cell law. -/
def weight (x : Nat) : Nat :=
  let good := ((List.range 4).filter (fun j ↦ digit x j < 2)).length
  1 + 20 * (2 * good - 4)

/-- Numerator of the public mass in one projected residue. -/
def marginal (j z : Nat) : Nat :=
  ((List.range 256).map (fun x ↦ if digit x j = z then weight x else 0)).sum

end SyndromePhaseGuard

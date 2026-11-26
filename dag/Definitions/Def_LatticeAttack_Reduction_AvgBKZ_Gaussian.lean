module

public import Mathlib

set_option autoImplicit true

public section

namespace SigabaNeo.AvgBKZ

/-- Deterministic error interval for a nonnegative weighted numerator once
Poisson summation bounds the mass by a relative error above its main term. -/
theorem gaussianRatioBounds {N Z M ε : ℝ} (hn : 0 ≤ N) (hm : 0 < M)
    (hl : M ≤ Z) (hu : Z ≤ M * (1 + ε)) :
    N / (M * (1 + ε)) ≤ N / Z ∧ N / Z ≤ N / M :=
  ⟨div_le_div_of_nonneg_left hn (hm.trans_le hl) hu,
   div_le_div_of_nonneg_left hn hm hl⟩

/-- A shortest-vector shell with 2k points of individual weight at most one,
in a unit-covolume block with mass at least s^k. -/
theorem gridShellWeightBound (k : ℕ) {s w Z : ℝ} (hs : 0 < s)
    (hw : w ≤ 1) (hz : s ^ k ≤ Z) :
    2 * (k : ℝ) * w / Z ≤ 2 * (k : ℝ) / s ^ k := by
  have hp : 0 < s ^ k := pow_pos hs _
  apply le_trans _ (div_le_div_of_nonneg_left (by positivity) hp hz)
  apply div_le_div_of_nonneg_right _ (hp.trans_le hz).le
  simpa using mul_le_mul_of_nonneg_left hw (show 0 ≤ 2 * (k : ℝ) by positivity)

#print axioms gaussianRatioBounds
#print axioms gridShellWeightBound

end SigabaNeo.AvgBKZ

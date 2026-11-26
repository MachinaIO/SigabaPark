import Mathlib

set_option autoImplicit true

namespace SigabaNeo.RevMink

/-- Convert a Gaussian mass budget on a finite region into a point count.
The exponent function may include the scale and a translation of the centre. -/
theorem card_le_of_gaussian_mass {α : Type*} (s : Finset α) (q : α → ℝ) (Q M : ℝ)
    (hQ : ∀ x ∈ s, q x ≤ Q) (hmass : ∑ x ∈ s, Real.exp (-q x) ≤ M) :
    (s.card : ℝ) ≤ M / Real.exp (-Q) := by
  apply (le_div_iff₀ (Real.exp_pos _)).2
  calc
    (s.card : ℝ) * Real.exp (-Q) = ∑ _x ∈ s, Real.exp (-Q) := by simp
    _ ≤ ∑ x ∈ s, Real.exp (-q x) :=
      Finset.sum_le_sum fun x hx ↦ Real.exp_le_exp.mpr (neg_le_neg (hQ x hx))
    _ ≤ M := hmass

#print axioms card_le_of_gaussian_mass

end SigabaNeo.RevMink

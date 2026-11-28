import Mathlib

theorem solution {R : Type} (rows : Finset R) (q : R → ℝ) (p : R → Bool) (D : R → Bool → ℝ) :
    ((∑ r ∈ rows, q r * (if p r then -(1-2*D r false) else (1-2*D r false))) +
     (∑ r ∈ rows, q r * (if p r then (1-2*D r true) else -(1-2*D r true)))) / 2 =
    ∑ r ∈ rows, q r * (D r (!(p r)) - D r (p r)) := by
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  cases p r <;> simp <;> ring

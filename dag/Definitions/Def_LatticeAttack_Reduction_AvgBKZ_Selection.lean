module

public import Mathlib

set_option autoImplicit true

public section

namespace SigabaNeo.AvgBKZ

/-- In the diagonal example each fixed event has one witness, while one adaptive
choice witnesses the event on every input. Counts are under the same sample space. -/
theorem diagonalSelectionCounts (n : ℕ) (i : Fin n) :
    (Finset.univ.filter (fun x : Fin n ↦ x = i)).card = 1 ∧
    (Finset.univ.filter (fun x : Fin n ↦ x = id x)).card = n := by
  have h : Finset.univ.filter (fun x : Fin n ↦ x = i) = {i} := by
    ext x
    simp
  simp [h]

/-- A positive diagonal weight can amplify the selected event. At diagonal weight
n+1, its conditional mass after normalization is exactly one half. -/
theorem diagonalWeightHalf (n : ℕ) (x : Fin (n + 2)) :
    2 * (n + 1) = ∑ i : Fin (n + 2), (1 + if i = x then n else 0) := by
  simp [Finset.sum_add_distrib]
  omega

#print axioms diagonalSelectionCounts
#print axioms diagonalWeightHalf

end SigabaNeo.AvgBKZ

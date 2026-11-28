import Mathlib

theorem solution (p b t : ℕ) (hp : 2 ∣ p) :
    (t < p ∧ (b+t)%2 = 1) ↔
    ∃! j : ℕ, j < p/2 ∧ t = 2*j+(b+1)%2 := by
  constructor
  · rintro ⟨ht, hodd⟩
    refine ⟨t/2, ⟨by omega, by omega⟩, ?_⟩
    rintro j ⟨_, hj⟩
    omega
  · rintro ⟨j, ⟨hj, ht⟩, _⟩
    omega

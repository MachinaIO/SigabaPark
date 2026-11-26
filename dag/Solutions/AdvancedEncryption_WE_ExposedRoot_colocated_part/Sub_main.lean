import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

theorem solution {R : Type*} [Ring R] {Q a n k : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype n]
    (β : Q → Matrix a n R) (π : Q) (Xc Xd : Matrix n k R) :
    (∑ q, β q * (if q = π then Xc else 0)) = β π * Xc ∧
    (∑ q, β q * (if q = π then Xd else 0)) = β π * Xd := by
  have key : ∀ X : Matrix n k R, (∑ q, β q * (if q = π then X else 0)) = β π * X := by
    intro X
    rw [Finset.sum_eq_single π]
    · simp
    · intro q _ hq
      simp [hq]
    · intro h
      exact absurd (Finset.mem_univ π) h
  exact ⟨key Xc, key Xd⟩

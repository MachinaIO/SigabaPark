import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.LinearCombination

theorem solution {R S : Type*} [CommRing R]
    (F : R → S) (hF : Function.Injective F) (s : R) :
    (∀ x y x' y' : R, F (x + y * s) = F (x' + y' * s) ↔ (x - x') + (y - y') * s = 0) ∧
    (∀ t : R, (∀ a b : R, a + b * s = 0 ↔ a + b * t = 0) → s = t) := by
  refine ⟨fun x y x' y' => ?_, fun t h => ?_⟩
  · rw [hF.eq_iff]
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  · have := (h (-s) 1).1 (by ring)
    linear_combination -this

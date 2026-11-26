import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Abel

open Matrix
open scoped BigOperators

theorem solution {R I J : Type*} [CommRing R] [Fintype I] [Fintype J] [DecidableEq J]
    (F : Matrix I J R) (y c : J → R) (u d : I → R) (s : R) (P : Finset J)
    (hy : F *ᵥ y = u) (hp : ∀ j ∈ P, c j = (d ᵥ* F) j) :
    (s - d ⬝ᵥ u) - ∑ j ∈ Finset.univ \ P, (c j - (d ᵥ* F) j) * y j = s - c ⬝ᵥ y := by
  classical
  have hz : ∑ j ∈ Finset.univ \ P, (c j - (d ᵥ* F) j) * y j =
      (c - d ᵥ* F) ⬝ᵥ y := by
    unfold dotProduct
    apply Finset.sum_subset (Finset.sdiff_subset ..)
    intro j hj hn
    have hP : j ∈ P := by simpa using hn
    simp [hp j hP]
  rw [hz, sub_dotProduct, ← Matrix.dotProduct_mulVec, hy]
  abel

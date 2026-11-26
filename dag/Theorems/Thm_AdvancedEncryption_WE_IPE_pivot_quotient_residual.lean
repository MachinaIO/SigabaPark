import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Abel

open Matrix
open scoped BigOperators

theorem AdvancedEncryption.WE.IPE.pivot_quotient_residual {R I J : Type*} [CommRing R] [Fintype I] [Fintype J] [DecidableEq J]
    (F : Matrix I J R) (y c : J → R) (u d : I → R) (s : R) (P : Finset J)
    (hy : F *ᵥ y = u) (hp : ∀ j ∈ P, c j = (d ᵥ* F) j) :
    (s - d ⬝ᵥ u) - ∑ j ∈ Finset.univ \ P, (c j - (d ᵥ* F) j) * y j = s - c ⬝ᵥ y := by
  sorry

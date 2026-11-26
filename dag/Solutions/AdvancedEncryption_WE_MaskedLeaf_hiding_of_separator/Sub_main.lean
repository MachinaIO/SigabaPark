import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

theorem solution {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {ι β : Type*} [AddCommMonoid β] {k n : ℕ} (c : ι → Fin k → R) (ℓ : Fin k → R)
    (hℓ : ∀ z, c z ⬝ᵥ ℓ = 1) (m m' : Fin n → R) (e : ι → Fin n → R)
    (F : (ι → Fin n → R) → β) :
    ∑ A : Matrix (Fin k) (Fin n) R, F (fun z => m + c z ᵥ* A + e z) =
      ∑ A : Matrix (Fin k) (Fin n) R, F (fun z => m' + c z ᵥ* A + e z) := by
  refine Fintype.sum_equiv (Equiv.addRight (vecMulVec ℓ (m - m'))) _ _ fun A => ?_
  congr 1
  funext z
  simp only [Equiv.coe_addRight, Matrix.vecMul_add, Matrix.vecMul_vecMulVec, hℓ, one_smul]
  abel

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

theorem solution {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {ι β : Type*} [DecidableEq ι] [AddCommMonoid β] {k n : ℕ} (c : ι → Fin k → R) (t : ι)
    (ℓ : Fin k → R) (ht : c t ⬝ᵥ ℓ = 1) (ho : ∀ z, z ≠ t → c z ⬝ᵥ ℓ = 0)
    (M : ι → Fin n → R) (m' : Fin n → R) (e : ι → Fin n → R)
    (F : (ι → Fin n → R) → β) :
    ∑ A : Matrix (Fin k) (Fin n) R, F (fun z => M z + c z ᵥ* A + e z) =
      ∑ A : Matrix (Fin k) (Fin n) R,
        F (fun z => Function.update M t m' z + c z ᵥ* A + e z) := by
  refine Fintype.sum_equiv (Equiv.addRight (vecMulVec ℓ (M t - m'))) _ _ fun A => ?_
  congr 1
  funext z
  simp only [Equiv.coe_addRight, Matrix.vecMul_add, Matrix.vecMul_vecMulVec]
  by_cases hz : z = t
  · subst hz; simp only [ht, one_smul, Function.update_self]; abel
  · simp only [ho z hz, zero_smul, Function.update_of_ne hz, add_zero]

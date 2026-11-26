import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring

open Matrix

theorem solution {K X Y ι : Type*} [Field K] [Fintype X] [Fintype Y] [Fintype ι]
    [DecidableEq ι] (u v : ι → K) (P₁ P₂ : X → Matrix ι ι K) (Q₁ Q₂ : Y → Matrix ι ι K) :
    (Matrix.of fun x y => u ⬝ᵥ ((P₁ x * Q₁ y * P₂ x * Q₂ y) *ᵥ v)).rank
      ≤ Fintype.card ι ^ 3 := by
  have key : ∀ (p w : ι → K) (A B : Matrix ι ι K),
      ((p ᵥ* A) ᵥ* B) ⬝ᵥ w = ∑ a, ∑ b, ∑ c, (p a * B b c) * (A a b * w c) := by
    intro p w A B
    simp only [dotProduct, vecMul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    ring
  have hfac : (Matrix.of fun x y => u ⬝ᵥ ((P₁ x * Q₁ y * P₂ x * Q₂ y) *ᵥ v))
      = Matrix.of (fun x (abc : ι × ι × ι) => (u ᵥ* P₁ x) abc.1 * P₂ x abc.2.1 abc.2.2)
        * Matrix.of (fun (abc : ι × ι × ι) y => Q₁ y abc.1 abc.2.1 * (Q₂ y *ᵥ v) abc.2.2) := by
    ext x y
    have h1 : u ⬝ᵥ ((P₁ x * Q₁ y * P₂ x * Q₂ y) *ᵥ v)
        = (((u ᵥ* P₁ x) ᵥ* Q₁ y) ᵥ* P₂ x) ⬝ᵥ (Q₂ y *ᵥ v) := by
      rw [dotProduct_mulVec, ← vecMul_vecMul, ← vecMul_vecMul, ← vecMul_vecMul,
        ← dotProduct_mulVec]
    rw [Matrix.of_apply, h1, key, Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    rfl
  rw [hfac]
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans ?_)
  simp [Fintype.card_prod, pow_succ, mul_assoc]

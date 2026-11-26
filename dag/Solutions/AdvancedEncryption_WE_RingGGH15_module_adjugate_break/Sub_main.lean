import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix in
theorem solution {R : Type*} [CommRing R] {k : Type*} [Fintype k] [DecidableEq k]
    (S0 S1 : Matrix k k R) (u a e0 e1 : k → R) :
    (S1.det • (u ᵥ* S0.adjugate)) ⬝ᵥ (S0 *ᵥ a + e0)
      - (S0.det • (u ᵥ* S1.adjugate)) ⬝ᵥ (S1 *ᵥ a + e1)
      = (S1.det • (u ᵥ* S0.adjugate)) ⬝ᵥ e0 - (S0.det • (u ᵥ* S1.adjugate)) ⬝ᵥ e1 := by
  have h0 : (S1.det • (u ᵥ* S0.adjugate)) ⬝ᵥ (S0 *ᵥ a) = (S1.det * S0.det) • (u ⬝ᵥ a) := by
    rw [dotProduct_mulVec, smul_vecMul, vecMul_vecMul, adjugate_mul,
      vecMul_smul, vecMul_one, smul_smul, smul_dotProduct]
  have h1 : (S0.det • (u ᵥ* S1.adjugate)) ⬝ᵥ (S1 *ᵥ a) = (S0.det * S1.det) • (u ⬝ᵥ a) := by
    rw [dotProduct_mulVec, smul_vecMul, vecMul_vecMul, adjugate_mul,
      vecMul_smul, vecMul_one, smul_smul, smul_dotProduct]
  rw [dotProduct_add, dotProduct_add, h0, h1, mul_comm S1.det S0.det]
  abel

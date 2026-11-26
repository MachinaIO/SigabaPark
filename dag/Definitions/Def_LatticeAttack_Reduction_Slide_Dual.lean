module

public import Definitions.Def_LatticeAttack_Reduction_Slide_SVP
import all Definitions.Def_LatticeAttack_Reduction_Slide_SVP

set_option autoImplicit true

@[expose] public section
namespace SigabaNeo.Slide

open Matrix
variable {n k d : ℕ}

/-- Rows reciprocal to the projected primal rows, in the same order. -/
def dualRows (A : Block k d) : Block k d := (dual A).transpose

theorem reciprocal_pairing (A : Block k d) (h : (A * A.transpose).det ≠ 0) :
    A * (dualRows A).transpose = 1 := by
  rw [dualRows, transpose_transpose, dual, ← Matrix.mul_assoc, inverse_right _ h]

theorem dualGram_regular (A : Block k d) (h : (A * A.transpose).det ≠ 0) :
    (dualRows A * (dualRows A).transpose).det ≠ 0 := by
  have pairing := reciprocal_pairing A h
  have expand : dualRows A = (inverse (A * A.transpose)).transpose * A := by
    rw [dualRows, dual, transpose_mul, transpose_transpose]
  nth_rw 1 [expand]
  rw [Matrix.mul_assoc, pairing, Matrix.mul_one, det_transpose]
  exact det_ne_zero_of_right_inverse (mul_eq_one_comm.mp (inverse_right _ h))

/-- Every vector in the rational row span having integral pairings with the primal rows
is the integer combination of reciprocal rows with precisely those coefficients. -/
theorem dual_represents (A : Block k d) (h : (A * A.transpose).det ≠ 0)
    (c : Fin k → ℚ) (z : Fin k → ℤ)
    (hz : (c ᵥ* A) ᵥ* A.transpose = fun i ↦ (z i : ℚ)) :
    vector (dualRows A) z = c ᵥ* A := by
  have pair : dualRows A * A.transpose = 1 := by
    simpa using congrArg Matrix.transpose (reciprocal_pairing A h)
  have e : dualRows A = (inverse (A * A.transpose)).transpose * A := by
    rw [dualRows, dual, transpose_mul, transpose_transpose]
  rw [e, Matrix.mul_assoc] at pair
  have right := mul_eq_one_comm.mp pair
  rw [vector, ← hz, e, vecMul_vecMul, vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc (_ * _), right, Matrix.one_mul]

def dualSolveAt (B : Matrix (Fin n) (Fin d) ℤ) (p k : ℕ) (fit : p + k ≤ n)
    (pos : 0 < k) :=
  shortest (dualRows (blockAt B p k fit)) (Pi.single ⟨0, pos⟩ 1)

theorem dualSolveAt_spec (B : Matrix (Fin n) (Fin d) ℤ) (p k : ℕ) (fit : p + k ≤ n)
    (pos : 0 < k) (h : ((blockAt B p k fit) * (blockAt B p k fit).transpose).det ≠ 0) :
    let D := dualRows (blockAt B p k fit)
    let s := dualSolveAt B p k fit pos
    vector D s ≠ 0 ∧ ∀ z : Fin k → ℤ, z ≠ 0 → weight D s ≤ weight D z := by
  obtain ⟨hn, hm⟩ := shortest_spec _ (dualGram_regular _ h)
    (Pi.single (⟨0, pos⟩ : Fin k) (1 : ℤ)) (by
      intro eq
      have := congrFun eq (⟨0, pos⟩ : Fin k)
      simp at this)
  exact ⟨vector_ne_zero _ (dualGram_regular _ h) _ hn, hm⟩

end SigabaNeo.Slide

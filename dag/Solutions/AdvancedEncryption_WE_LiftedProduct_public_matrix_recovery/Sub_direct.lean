import Mathlib
import CslibFrontier.Foundations.Algebra.Negacyclic
open Cslib Finset

theorem solution {n : ℕ} (a s : Fin n → ℤ) (i : Fin n) (flag : Bool) :
    let b (j : Fin n) := if flag then (if 0 ≤ a j then a j-128 else a j+128) else a j
    negacyclicMul (fun j => (a j : ZMod 256)) (fun j => (s j : ZMod 256)) i =
      negacyclicMul (fun j => (b j : ZMod 256)) (fun j => (s j : ZMod 256)) i +
        (if flag then 128 * (((∑ j, s j) % 2 : ℤ) : ZMod 256) else 0) := by
  have correction {n : ℕ} (a s : Fin n → ZMod 256) (i : Fin n) :
      negacyclicMul (a + (fun _ => (128 : ZMod 256))) s i =
        negacyclicMul a s i + 128 * ∑ j, s j := by
    rw [add_negacyclicMul, Pi.add_apply]
    congr 1
    simp only [negacyclicMul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have e : -(128:ZMod 256)=128 := by decide
    simp [rotMatrix, Matrix.of_apply, e]
  
  intro b
  cases flag with
  | false => simp [b]
  | true =>
    have ha : (fun j => (a j : ZMod 256)) = ((fun j => (b j : ZMod 256)) + fun _ => 128) := by
      funext j
      simp only [Pi.add_apply, b, ↓reduceIte]
      have e : (128:ZMod 256)+128=0 := by decide
      split_ifs <;> push_cast
      · ring
      · rw [add_assoc, e, add_zero]
    rw [ha, correction]
    simp only [↓reduceIte]
    congr 1
    rw [← Int.cast_sum]
    let z := ∑ j, s j
    have hz : z = 2 * (z/2) + z%2 := by omega
    have e : (128:ZMod 256)*2=0 := by decide
    change 128*(z:ZMod 256) = 128*((z%2:ℤ):ZMod 256)
    conv_lhs => rw [hz]
    push_cast
    rw [mul_add, ←mul_assoc, e, zero_mul, zero_add]

import Mathlib
import CslibFrontier.Foundations.Algebra.Negacyclic
open Cslib Finset

theorem AdvancedEncryption.WE.LiftedProduct.public_matrix_recovery {n : ℕ} (a s : Fin n → ℤ) (i : Fin n) (flag : Bool) :
    let b (j : Fin n) := if flag then (if 0 ≤ a j then a j-128 else a j+128) else a j
    negacyclicMul (fun j => (a j : ZMod 256)) (fun j => (s j : ZMod 256)) i =
      negacyclicMul (fun j => (b j : ZMod 256)) (fun j => (s j : ZMod 256)) i +
        (if flag then 128 * (((∑ j, s j) % 2 : ℤ) : ZMod 256) else 0) := by sorry

import Mathlib
import CslibFrontier.Foundations.Algebra.Negacyclic
open Cslib Finset

theorem AdvancedEncryption.WE.LiftedProduct.folded_bound {n : ℕ} (a s : Fin n → ℤ) (ha : ∀ i, -128 ≤ a i ∧ a i < 128)
    (hs : ∀ i, |s i| ≤ (1 : ℕ)) :
    let a' (i : Fin n) := if 0 ≤ a i then a i-128 else a i+128
    let b := if (∑ i, |a' i|) < ∑ i, |a i| then a' else a
    ∀ i, 2*|negacyclicMul b s i| ≤ (n : ℤ)*128 := by sorry

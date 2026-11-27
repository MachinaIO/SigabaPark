import Mathlib
import CslibFrontier.Foundations.Algebra.Negacyclic
open Cslib Finset

theorem solution {n : ℕ} (a s : Fin n → ℤ) (ha : ∀ i, -128 ≤ a i ∧ a i < 128)
    (hs : ∀ i, |s i| ≤ (1 : ℕ)) :
    let a' (i : Fin n) := if 0 ≤ a i then a i-128 else a i+128
    let b := if (∑ i, |a' i|) < ∑ i, |a i| then a' else a
    ∀ i, 2*|negacyclicMul b s i| ≤ (n : ℤ)*128 := by
  intro a' b i
  have eq : (∑ j, |a j|) + (∑ j, |a' j|) = (n : ℤ)*128 := by
    rw [← sum_add_distrib]
    have hterm (j : Fin n) : |a j|+|a' j|=128 := by
      have h := ha j
      dsimp [a']
      by_cases hn : 0 ≤ a j
      · rw [if_pos hn, abs_of_nonneg hn, abs_of_nonpos (by omega)]
        omega
      · rw [if_neg hn, abs_of_nonpos (by omega), abs_of_nonneg (by omega)]
        omega
    simp_rw [hterm]
    simp
  have hb : 2*(∑ j, |b j|) ≤ (n:ℤ)*128 := by
    dsimp [b]
    split_ifs <;> omega
  have h := abs_negacyclicMul_le_sum_abs_mul (a:=b) (β:=1) hs i
  simp only [Nat.cast_one, mul_one] at h
  omega

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Fintype.Basic

theorem solution {M : Type} [AddCommMonoid M] (p k : ℕ) (v : Fin p → Bool)
    (T : Fin p → Fin (k+1) → M) :
    (∑ i : Fin p, ∑ j : Fin (k+1), if (v i).toNat.testBit j.val then T i j else 0) =
      ∑ i : Fin p, if v i then T i 0 else 0 := by
  apply Finset.sum_congr rfl
  intro i _
  cases v i with
  | false => simp
  | true =>
    simp only [Bool.toNat_true, ite_true]
    rw [Finset.sum_eq_single (0 : Fin (k+1))]
    · simp
    · intro j _ hj
      have h : j.val ≠ 0 := fun e ↦ hj (Fin.ext e)
      simp [Nat.testBit_one_eq_true_iff_self_eq_zero, h]
    · simp

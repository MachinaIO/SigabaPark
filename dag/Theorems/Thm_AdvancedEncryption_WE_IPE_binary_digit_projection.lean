import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Fintype.Basic

theorem AdvancedEncryption.WE.IPE.binary_digit_projection {M : Type} [AddCommMonoid M] (p k : ℕ) (v : Fin p → Bool)
    (T : Fin p → Fin (k+1) → M) :
    (∑ i : Fin p, ∑ j : Fin (k+1), if (v i).toNat.testBit j.val then T i j else 0) =
      ∑ i : Fin p, if v i then T i 0 else 0 := by
  sorry

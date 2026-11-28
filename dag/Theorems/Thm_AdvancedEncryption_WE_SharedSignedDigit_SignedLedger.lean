import Mathlib

theorem AdvancedEncryption.WE.SharedSignedDigit.SignedLedger (n : ℕ) (Q β : ℤ) (a t : Fin n → ℤ) :
    2*Q*β + ∑ i, (1-2*t i)*(Q+a i) =
      (∑ i, (Q+a i)) - 2*(∑ i, t i*a i) + 2*Q*(β-∑ i, t i) := by sorry

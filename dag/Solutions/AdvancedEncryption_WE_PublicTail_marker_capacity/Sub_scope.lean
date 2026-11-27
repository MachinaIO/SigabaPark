import Mathlib

theorem solution (b h k : ℕ) (decode : Fin (2^k) → Fin (2^b) → Fin (2^h))
    (onto : Function.Surjective decode) : h*2^b ≤ k := by
  have hs := Fintype.card_le_of_surjective decode onto
  have bound : ((2:ℕ)^h)^(2^b) ≤ 2^k := by simpa [Fintype.card_fun] using hs
  rw [← pow_mul] at bound
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp bound

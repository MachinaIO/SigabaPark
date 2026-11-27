import Mathlib

theorem solution {K : Type} [Fintype K] [DecidableEq K] (test : K → K × K) :
    ((Finset.univ.image test).card) * Fintype.card K ≤ Fintype.card (K × K) := by
  rw [Fintype.card_prod]
  apply Nat.mul_le_mul_right
  exact (Finset.card_image_le).trans_eq (Finset.card_univ)

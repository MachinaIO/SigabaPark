import Mathlib

theorem AdvancedEncryption.WE.JoinRoute.public_check_image {K : Type} [Fintype K] [DecidableEq K] (test : K → K × K) :
    ((Finset.univ.image test).card) * Fintype.card K ≤ Fintype.card (K × K) := by
  sorry

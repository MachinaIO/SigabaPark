import Mathlib

theorem AdvancedEncryption.WE.SuccinctPacket.quadratic_decoder {K P L : Type} [CommSemiring K] [Fintype P] [Fintype L] (a b : L → P → K) (c : P → K)
    (u : P → K) :
    (∑ i, u i * c i) + (∑ l, (∑ i, u i * a l i) * (∑ j, u j * b l j)) =
    (∑ i, u i * c i) + ∑ i, ∑ j, (u i * u j) * (∑ l, a l i * b l j) := by sorry

import Mathlib

theorem AdvancedEncryption.WE.SealedRow.selected_phase_parity {ι : Type*} (I : Finset ι) (hI : I.card ≤ 129)
    (dot bit err : ι → ℤ) (wrap : ℤ) (he : ∀ i ∈ I, -63 ≤ err i ∧ err i ≤ 63) :
    ((∑ i ∈ I, (dot i + 16384 * bit i + err i)) - (∑ i ∈ I, dot i) +
      32768 * wrap + 8192) / 16384 % 2 = (∑ i ∈ I, bit i) % 2 := by sorry

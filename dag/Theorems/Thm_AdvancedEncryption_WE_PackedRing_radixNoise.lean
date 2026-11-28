import Definitions.Def_PackedRingPacket
open scoped BigOperators
open Cslib Cslib.Probability

theorem AdvancedEncryption.WE.PackedRing.radixNoise {n d T : ℕ} (E Z : Fin d→Fin n→ℤ)
    (he : ∑ i, ∑ j, |E i j|≤(T:ℤ)) (hz : ∀ i j, |Z i j|≤8) (j : Fin n) :
    |∑ i, negacyclicMul (E i) (Z i) j| ≤ 8*(T:ℤ) := by sorry

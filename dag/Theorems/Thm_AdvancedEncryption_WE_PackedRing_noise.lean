import Definitions.Def_PackedRingPacket
open scoped BigOperators
open Cslib Cslib.Probability

theorem AdvancedEncryption.WE.PackedRing.noise {n d T : ℕ} (E Z : Fin d→Fin n→ℤ)
    (he : ∀ i j, |E i j|≤T) (hz : ∀ i j, |Z i j|≤1) (j : Fin n) :
    |∑ i, negacyclicMul (E i) (Z i) j| ≤ (d:ℤ)*n*T := by sorry

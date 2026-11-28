import Definitions.Def_PackedRingPacket
open scoped BigOperators
open Cslib Cslib.Probability

theorem AdvancedEncryption.WE.PackedRing.singleCoeff {n : ℕ} {R : Type*} [CommRing R] (a : Fin n → R) (m : R) (j : Fin n) :
    negacyclicMul a (m • (1 : Negacyclic R n).coeffs) j=m*a j := by sorry

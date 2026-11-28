import Definitions.Def_PackedRingPacket
open scoped BigOperators
open Cslib Cslib.Probability

theorem AdvancedEncryption.WE.PackedRing.productPhase {R : Type*} [CommRing R] {d : ℕ}
    (s mu left right : R) (z A E gu gv : Fin d → R)
    (hl : ∑ i, gu i*z i=left) (hr : ∑ i, gv i*z i=right) :
    (∑ i, (s*A i+E i+mu*gv i)*z i)-s*(∑ i, (A i+mu*gu i)*z i)
      = mu*(right-s*left)+∑ i, E i*z i := by sorry

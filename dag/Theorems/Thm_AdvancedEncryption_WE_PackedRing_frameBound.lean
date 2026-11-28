import Definitions.Def_PackedRingPacket
open scoped BigOperators
open Cslib Cslib.Probability

theorem AdvancedEncryption.WE.PackedRing.frameBound (ct : List Bool) (h : ct.length=RingPacket.bankBits 1024 26 1024) :
    (SigabaNeo.encodeTuple [ct]).length>2^32 := by sorry

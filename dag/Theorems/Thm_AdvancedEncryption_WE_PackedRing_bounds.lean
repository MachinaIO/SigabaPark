import Definitions.Def_PackedRingPacket
open scoped BigOperators
open Cslib Cslib.Probability

theorem AdvancedEncryption.WE.PackedRing.bounds :
    RingPacket.bankBits 1024 20 1024=1677721600 ∧
    RingPacket.bankBits 1024 26 1024=2835349504 ∧
    2*RingPacket.bankBits 1024 26 1024+1>2^32 ∧
    2*RingPacket.bankBits 1024 20 1024+1+2*RingPacket.bankBits 1024 20 1023>2^32 ∧
    RingPacket.bankBits 1024 26 1+2*1024*26=2822144 ∧
    1024*200+2*26*1024*200<2^26/4 := by sorry

import Definitions.Def_CanonBroadcastRoles

open BroadcastWire SigabaNeo Turing.MultiTapeTM AdvancedEncryption.WE.CircuitSAT

theorem AdvancedEncryption.WE.CanonicalBroadcast.costs :
    CanonicalBroadcast.enc.time=105000000 ∧ CanonicalBroadcast.dec.time=210000000 ∧
    CanonicalBroadcast.enc.descLen=2366878644 ∧ CanonicalBroadcast.dec.descLen=294 ∧
    CanonicalBroadcast.enc.cost+CanonicalBroadcast.dec.cost=2681878938 ∧
    CanonicalTaggedBroadcast.enc.time=105000000 ∧ CanonicalTaggedBroadcast.dec.time=210000000 ∧
    CanonicalTaggedBroadcast.enc.descLen=3819572496 ∧ CanonicalTaggedBroadcast.dec.descLen=294 ∧
    CanonicalTaggedBroadcast.enc.cost+CanonicalTaggedBroadcast.dec.cost=4134572790 ∧
    4134572790 < 2^32 := by sorry

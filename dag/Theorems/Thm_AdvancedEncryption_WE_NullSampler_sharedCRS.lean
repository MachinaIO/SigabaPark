import Definitions.Def_NullSamplerCosts
open OneBitSampler
theorem AdvancedEncryption.WE.NullSampler.sharedCRS (G Q m L : Nat) (cover : 2^128 ≤ G*Q*m) (modulusBits : 128≤L) :
    2^100 < Q*m*L + G*m^2*L^2 + G*Q*L := by sorry

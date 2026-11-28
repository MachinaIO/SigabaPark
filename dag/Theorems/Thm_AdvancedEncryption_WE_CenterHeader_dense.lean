import Definitions.Def_AffineCenterHeader

open AffineCenterHeader

set_option exponentiation.threshold 1024

theorem AdvancedEncryption.WE.CenterHeader.dense (m q L : Nat) (hl : 1 ≤ L)
    (hm : 64 * L^2 ≤ m) (hq : 8*m^2 ≤ q) (hb : q < 2^(L+1)) :
    2^32 < m^2 := by sorry

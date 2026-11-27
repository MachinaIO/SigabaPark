import Definitions.Def_AffineCenterHeader

open AffineCenterHeader

set_option exponentiation.threshold 1024

theorem solution : 24*10 + (32*9+24*10) + 1 = 769 ∧
    769^24*2^256 < (257^4-1)^8*(769^4-1)^6 := by
  decide

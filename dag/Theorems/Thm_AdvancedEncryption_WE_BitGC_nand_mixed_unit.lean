import Mathlib

theorem AdvancedEncryption.WE.BitGC.nand_mixed_unit (u v : ℤ) (hu : u = 0 ∨ u = 1) (hv : v = 0 ∨ v = 1) :
    ((1-u*v) + (1-(1-u)*(1-v)) - (1-(1-u)*v) - (1-u*(1-v)))^2 = 1 := by sorry

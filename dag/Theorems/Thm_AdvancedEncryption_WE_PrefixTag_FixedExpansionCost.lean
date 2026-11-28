import Mathlib

theorem AdvancedEncryption.WE.PrefixTag.FixedExpansionCost :
    512*7+2*8*512 = (11776 : Nat) ∧
    2*(11776+1) ≤ 8*512*7 ∧
    8*512*7+2*(11776+1) = (52226 : Nat) ∧
    2*13*8*512^2 = (54525952 : Nat) := by sorry

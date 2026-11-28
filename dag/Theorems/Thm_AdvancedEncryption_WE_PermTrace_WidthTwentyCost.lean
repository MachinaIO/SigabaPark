import Mathlib

theorem AdvancedEncryption.WE.PermTrace.WidthTwentyCost :
    6 * (4 * 16 - 4)^3 = (1296000 : Nat) ∧
    2^60 < Nat.factorial 20 / 2 ∧ Nat.factorial 20 / 2 ≤ 2^61 ∧
    1296000 * (2*61 + 13) = (174960000 : Nat) ∧
    2 * 174960000 + 1 < (2 : Nat)^32 := by sorry

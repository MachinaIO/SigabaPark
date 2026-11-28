import Mathlib

theorem AdvancedEncryption.WE.PermTrace.CrtCleanCost :
    (∀ v : Fin 4097, (v.val % 13 = 0 ∧ v.val % 17 = 0 ∧ v.val % 19 = 0) ↔ v.val = 0) ∧
    4 * (3 * 6 * 4096) + 4 = (294916 : Nat) ∧
    Nat.factorial 51 ≤ 2^220 ∧ 2^219 < Nat.factorial 51 ∧
    2 * (294916 * (2*220+13)) + 1 = (267193897 : Nat) := by sorry

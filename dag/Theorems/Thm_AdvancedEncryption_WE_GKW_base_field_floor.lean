import Mathlib.Tactic

theorem AdvancedEncryption.WE.GKW.base_field_floor (levels n m width outputs : ℕ)
    (hn : (12 * levels) ^ 2 ≤ n) (hm : 5 * n ≤ m)
    (hw : 12 * levels ≤ width) (hr : n * m * (12 * levels) ≤ outputs) :
    25 * (12 * levels) ^ 10 ≤ outputs * (n * m * width) ∧
    (1 ≤ levels → 3748295401 < 4 * (outputs * (n * m * width))) ∧
    (62 ≤ levels → 2 ^ 100 < outputs * (n * m * width)) ∧
    (256 ≤ levels → 2 ^ 120 < outputs * (n * m * width)) := by sorry

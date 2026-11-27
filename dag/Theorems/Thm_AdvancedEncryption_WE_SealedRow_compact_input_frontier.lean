import Mathlib

theorem AdvancedEncryption.WE.SealedRow.compact_input_frontier :
    let table := fun b : Fin 129 ↦ 2 ^ b.val * 256 * 8 * (2048 + (b.val + 1) * 1024 + 1)
    let seed := fun b : Fin 129 ↦ (129 - b.val) * 3072
    let payload := fun b : Fin 129 ↦ 2 * (table b + seed b * 1032 + 128 * 1065024) + 1
    (∀ b, payload b ≤ 2 ^ 32 ↔ b.val ≤ 6) ∧
    (∀ b, 1103171585 ≤ payload b) ∧ payload 0 = 1103171585 ∧ payload 1 = 1117806593 ∧
    (∀ b, 0 < b.val → 1117806593 ≤ payload b) ∧
    (∀ b, payload b ≤ 2 ^ 32 → 14 * (2 ^ 32 - payload b) < seed b * 1065024) := by sorry

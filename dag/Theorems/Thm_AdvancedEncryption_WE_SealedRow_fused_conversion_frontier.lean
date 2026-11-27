import Mathlib

theorem AdvancedEncryption.WE.SealedRow.fused_conversion_frontier (h : ℕ) :
    let table := fun b : Fin 129 ↦ 2 ^ b.val * 256 * 8 * (2048 + (b.val + 1) * 1024 + 1)
    let payload := fun b : Fin 129 ↦ 2 * (table b + (129 - b.val) * 3072 * 1935 + 128 * 1065024) + 1
    (∀ b, payload b ≤ 2 ^ 32 ↔ b.val ≤ 6) ∧
    (∀ b, 2 ^ 32 < payload b + 3072 * 1065024) ∧
    (∀ b, payload b + 3072 * 1065024 / 2 ≤ 2 ^ 32 ↔ b.val ≤ 4) ∧
    (∀ b, 0 < b.val → payload 1 ≤ payload b) ∧ payload 1 = 1827954689 ∧
    (∀ b, payload b ≤ 2 ^ 32 →
      14 * (2 ^ 32 - payload b) < 11 * 3072 * 1065024) ∧
    ((∃ b : Fin 129, 2 * (table b + (129 - b.val) * h * 1935 + 128 * 1065024) + 1
      ≤ 2 ^ 32) ↔ h ≤ 8052) ∧
    (∀ b : Fin 129, 4871446529 ≤
      2 * (table b + (129 - b.val) * 9216 * 1935 + 128 * 1065024) + 1) := by sorry

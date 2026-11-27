import Mathlib

theorem AdvancedEncryption.WE.SealedRow.encoded_frontier (W : ℕ) :
    let table := fun b : Fin 129 ↦ 2 * (2 ^ b.val * 256 * 8 * (2048 + (b.val + 1) * 1024 + 1)) + 1
    let dense := fun b : Fin 129 ↦ (129 - b.val) * 6144
    let shortSeed := fun b : Fin 129 ↦ if b.val = 128 then 6144 else 12288
    (∀ b, table b ≤ 2 ^ 32 ↔ b.val ≤ 6) ∧
    ((∃ b, table b + dense b * W ≤ 2 ^ 32) ↔ W ≤ 5418) ∧
    ((∃ b, table b + shortSeed b * W ≤ 2 ^ 32) ↔ W ≤ 348500) ∧
    (∀ b, 803576610817 ≤ table b + dense b * 1065024) ∧
    table 8 + dense 8 * 1065024 = 803576610817 := by sorry

import Mathlib

theorem solution (h : ℕ) :
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
      2 * (table b + (129 - b.val) * 9216 * 1935 + 128 * 1065024) + 1) := by
  dsimp only
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ⟨?_, ?_⟩, by decide⟩
  · rintro ⟨b, hb⟩
    by_contra! bad
    have lower : ∀ j : Fin 129, 2 ^ 32 <
        2 * (2 ^ j.val * 256 * 8 * (2048 + (j.val + 1) * 1024 + 1) +
          (129 - j.val) * 8053 * 1935 + 128 * 1065024) + 1 := by decide
    have hm := Nat.mul_le_mul_right 1935 (Nat.mul_le_mul_left (129 - b.val) bad)
    have hb' := lower b
    omega
  · intro hh
    refine ⟨1, ?_⟩
    change 2 * (16781312 + 128 * h * 1935 + 128 * 1065024) + 1 ≤ 2 ^ 32
    omega

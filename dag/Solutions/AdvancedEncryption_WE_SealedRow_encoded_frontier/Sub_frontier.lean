import Mathlib

theorem solution (W : ℕ) :
    let table := fun b : Fin 129 ↦ 2 * (2 ^ b.val * 256 * 8 * (2048 + (b.val + 1) * 1024 + 1)) + 1
    let dense := fun b : Fin 129 ↦ (129 - b.val) * 6144
    let shortSeed := fun b : Fin 129 ↦ if b.val = 128 then 6144 else 12288
    (∀ b, table b ≤ 2 ^ 32 ↔ b.val ≤ 6) ∧
    ((∃ b, table b + dense b * W ≤ 2 ^ 32) ↔ W ≤ 5418) ∧
    ((∃ b, table b + shortSeed b * W ≤ 2 ^ 32) ↔ W ≤ 348500) ∧
    (∀ b, 803576610817 ≤ table b + dense b * 1065024) ∧
    table 8 + dense 8 * 1065024 = 803576610817 := by
  dsimp only
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · decide
  · rintro ⟨b, hb⟩
    by_contra! h
    have hi : ∀ j : Fin 129, 2 ^ 32 <
        2 * (2 ^ j.val * 256 * 8 * (2048 + (j.val + 1) * 1024 + 1)) + 1 +
          (129 - j.val) * 6144 * 5419 := by decide
    exact (Nat.not_lt_of_ge hb) ((hi b).trans_le
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _))
  · intro h
    exact ⟨1, (Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _).trans (by decide)⟩
  · rintro ⟨b, hb⟩
    by_contra! h
    have hi : ∀ j : Fin 129, 2 ^ 32 <
        2 * (2 ^ j.val * 256 * 8 * (2048 + (j.val + 1) * 1024 + 1)) + 1 +
          (if j.val = 128 then 6144 else 12288) * 348501 := by decide
    exact (Nat.not_lt_of_ge hb) ((hi b).trans_le
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _))
  · intro h
    exact ⟨0, (Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _).trans (by decide)⟩
  · decide
  · decide

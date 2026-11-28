import Mathlib

theorem solution {K V ι : Type*} [Field K] [DecidableEq K] [AddCommGroup V] [Module K V]
    (d : ι → K) (x : ι → V) (g : V) (f : V →ₗ[K] K) (hx : ∀ i, d i = 0 → x i = 0) :
    (∀ i, f (if d i = 0 then g else (d i)⁻¹ • x i) = 0) ↔
    (∀ i, f (x i) = 0) ∧ ((∃ i, d i = 0) → f g = 0) := by
  constructor
  · intro h
    constructor
    · intro i
      by_cases hd : d i = 0
      · simp [hx i hd]
      · simpa [hd, map_smul] using h i
    · rintro ⟨i, hd⟩
      simpa [hd] using h i
  · rintro ⟨h, hg⟩ i
    by_cases hd : d i = 0
    · simpa [hd] using hg ⟨i, hd⟩
    · simp [hd, h]

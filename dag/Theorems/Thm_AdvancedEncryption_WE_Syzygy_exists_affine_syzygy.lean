import Mathlib

/-- Affine short syzygy (pigeonhole): among `M` integer vectors in `[-B, B]^d`, if
`(2MB+1)^d (M+1) < 2^M`, some nonzero `{-1,0,1}` combination with coefficient sum `0` vanishes.
Used in the note `pq-we-affine-syzygy-barrier`. -/
theorem AdvancedEncryption.WE.Syzygy.exists_affine_syzygy {M d : ℕ} (B : ℕ)
    (v : Fin M → Fin d → ℤ) (hv : ∀ j i, |v j i| ≤ B)
    (hM : (2 * M * B + 1) ^ d * (M + 1) < 2 ^ M) :
    ∃ α : Fin M → ℤ, α ≠ 0 ∧ (∀ j, |α j| ≤ 1) ∧ ∑ j, α j = 0 ∧ ∑ j, α j • v j = 0 := by sorry

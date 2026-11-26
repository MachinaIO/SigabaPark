import Mathlib

/-- Fresh indices are few: in a finite-dimensional vector space, the indices `r` such that `v r` is
not in the span of the later vectors `v t` (`t > r`) number at most the dimension. Over a field this
is the counting step of the affine-syzygy argument with no coefficient bound: for a uniformly random
planted position `r` among `M`, `v r` lies in the span of the later ones with probability
`≥ 1 − dim/M`. Used in the note `pq-we-non-lattice-algebras`. -/
theorem AdvancedEncryption.WE.Codes.card_fresh_le_finrank {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {M : ℕ} (v : Fin M → V) :
    {r | v r ∉ Submodule.span K (v '' {t | r < t})}.ncard ≤ Module.finrank K V := by sorry

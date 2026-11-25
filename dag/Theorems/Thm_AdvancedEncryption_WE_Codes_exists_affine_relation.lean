import Mathlib

/-- Affine relation over a field: among `N > d + 1` vectors of `K^d` there is a nonzero
combination with coefficient sum `0` that vanishes exactly (found by Gaussian elimination). No
bound on the coefficients is needed, unlike the integer pigeonhole
`AdvancedEncryption.WE.Syzygy.exists_affine_syzygy`. Used in the note `pq-we-non-lattice-algebras`
(public linear zero tests of LPN/code encodings have exact fake zeros). -/
theorem AdvancedEncryption.WE.Codes.exists_affine_relation {K : Type*} [Field K] {N d : ℕ}
    (z : Fin N → Fin d → K) (hN : d + 1 < N) :
    ∃ α : Fin N → K, α ≠ 0 ∧ ∑ j, α j = 0 ∧ ∑ j, α j • z j = 0 := by sorry

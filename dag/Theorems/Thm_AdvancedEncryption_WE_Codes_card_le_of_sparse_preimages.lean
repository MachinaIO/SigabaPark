import Mathlib

/-- Sparse preimages are expensive: if every element of a finite set `T` has a preimage under
`f : (Fin N → F) → T` with at most `ρ` nonzero entries, then `|T| ≤ ((N + 1) |F|)^ρ`. For a linear
`f` onto `F^n` this forces `ρ ≥ n log|F| / log((N + 1)|F|)`: a Hamming-metric "gadget" with sparse
preimages of every target needs heavy columns. Used in the note `pq-we-non-lattice-algebras`
(no BGG+-type evaluation for LPN and codes). -/
theorem AdvancedEncryption.WE.Codes.card_le_of_sparse_preimages {F : Type*} [AddCommMonoid F]
    [Fintype F] [DecidableEq F] {T : Type*} [Fintype T] {N ρ : ℕ} (f : (Fin N → F) → T)
    (hf : ∀ t, ∃ x, f x = t ∧ (Finset.univ.filter fun j => x j ≠ 0).card ≤ ρ) :
    Fintype.card T ≤ ((N + 1) * Fintype.card F) ^ ρ := by sorry

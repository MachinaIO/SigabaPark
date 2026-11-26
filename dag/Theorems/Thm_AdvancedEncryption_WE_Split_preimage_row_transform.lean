import SigabaNeoStd.Lattices.Trapdoor

open Matrix SigabaNeo.Lattices

/-- **Row transforms do not change preimages.** For an invertible `T` (unit determinant over
`ℤ_q`), `Trapdoor.preimage (T B) (T P) τ = Trapdoor.preimage B P τ`. This is the step that makes
a CVW18-style masking row block collapse back to the unmasked GGH15 level when the leaf must be
decryptable (note `pq-we-split-lemma-attempts`, approach 2). -/
theorem AdvancedEncryption.WE.Split.preimage_row_transform {n m k q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q))
    (T : Matrix (Fin n) (Fin n) (ZMod q)) (hT : IsUnit T.det) (P : Matrix (Fin n) (Fin k) (ZMod q))
    (τ : ℝ) (hτ : 0 < τ) :
    Trapdoor.preimage (T * B) (T * P) τ hτ = Trapdoor.preimage B P τ hτ := by sorry

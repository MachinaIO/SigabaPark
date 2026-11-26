import SigabaNeoStd.Lattices.Trapdoor

open Matrix SigabaNeo.Lattices

/-- **Gaussian preimages depend only on the cosets.** If, column by column, the cosets
`{x ∈ ℤ^m : B x = P_j}` and `{x : B' x = P'_j}` are the same set (the matrices may have different
numbers of rows), then the coset Gaussian preimage laws `Trapdoor.preimage B P τ` and
`Trapdoor.preimage B' P' τ` are equal. In a GGH15 encoding `D ← A^{-1}(Y)`, any change of the
stacked matrix and targets that keeps the solution set of `A D = Y` leaves the law of `D`
unchanged (note `pq-we-split-lemma-attempts`). -/
theorem AdvancedEncryption.WE.Split.preimage_congr {n n' m k q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q))
    (B' : Matrix (Fin n') (Fin m) (ZMod q)) (P : Matrix (Fin n) (Fin k) (ZMod q))
    (P' : Matrix (Fin n') (Fin k) (ZMod q)) (τ : ℝ) (hτ : 0 < τ)
    (h : ∀ (j : Fin k) (x : Fin m → ℤ), B *ᵥ (fun i => (x i : ZMod q)) = (fun i => P i j) ↔
      B' *ᵥ (fun i => (x i : ZMod q)) = (fun i => P' i j)) :
    Trapdoor.preimage B P τ hτ = Trapdoor.preimage B' P' τ hτ := by sorry

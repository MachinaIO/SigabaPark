import SigabaNeoStd.Lattices.Trapdoor

open Matrix SigabaNeo.Lattices

/-- **A correlated copy adds no constraint.** Stacking the rows `R B` under `B` and the targets
`R P` under `P` leaves the coset Gaussian preimage law unchanged:
`Trapdoor.preimage [B; R B] [P; R P] τ = Trapdoor.preimage B P τ`. In the positional GGH15
witness-encryption candidate, a state `σ'` whose row block is `R A^{(σ)}` and whose outgoing
targets are `R Y_σ` (a correlated copy of `σ`) therefore gives exactly the law of the merged
hybrid: the split lemma is "correlated copy ≈ independent copy" (note
`pq-we-split-lemma-attempts`). -/
theorem AdvancedEncryption.WE.Split.preimage_correlated_copy {n n' m k q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q))
    (R : Matrix (Fin n') (Fin n) (ZMod q)) (P : Matrix (Fin n) (Fin k) (ZMod q))
    (τ : ℝ) (hτ : 0 < τ) :
    Trapdoor.preimage (Matrix.of fun i j => Fin.addCases (fun a => B a j) (fun b => (R * B) b j) i)
        (Matrix.of fun i j => Fin.addCases (fun a => P a j) (fun b => (R * P) b j) i) τ hτ =
      Trapdoor.preimage B P τ hτ := by sorry

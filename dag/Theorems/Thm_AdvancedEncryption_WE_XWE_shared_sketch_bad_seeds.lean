import SigabaNeoStd

theorem AdvancedEncryption.WE.XWE.shared_sketch_bad_seeds {T V S : Type*} [DecidableEq V] [DecidableEq S]
    (cert : Finset T) (res : T → Finset V) (bad : V → Finset S) (B D : ℕ)
    (hsize : ∀ t ∈ cert, (res t).card ≤ D)
    (hhash : ∀ t ∈ cert, ∀ v ∈ res t, (bad v).card ≤ B) :
    (cert.biUnion fun t ↦ (res t).biUnion bad).card ≤ cert.card * D * B := by
  sorry

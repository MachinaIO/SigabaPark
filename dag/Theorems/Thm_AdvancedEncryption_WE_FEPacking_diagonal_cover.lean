import Mathlib.Data.Fintype.Card

theorem AdvancedEncryption.WE.FEPacking.diagonal_cover {I : Type} (n : I → ℕ) (hn : ∀ i, 0 < n i) (q : ℕ)
    (hq : ∀ i, n i ≤ q) (Y : I → Type) (row : ∀ i, Fin (n i) → Y i)
    (agg : (∀ i, Fin (n i)) → ∀ i, Y i)
    (sep : ∀ v i, agg v i = row i (v i)) :
    (∀ i (a : Fin (n i)), a.val < q ∧
      agg (fun j => ⟨a.val % n j, Nat.mod_lt _ (hn j)⟩) i = row i a) ∧
    (∀ (m : ℕ) (schedule : Fin m → (i : I) → Fin (n i)),
      (∀ i, Function.Surjective (fun z => schedule z i)) → ∀ i, n i ≤ m) := by
  sorry

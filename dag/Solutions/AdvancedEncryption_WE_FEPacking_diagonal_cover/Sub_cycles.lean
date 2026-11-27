import Mathlib.Data.Fintype.Card

theorem solution {I : Type} (n : I → ℕ) (hn : ∀ i, 0 < n i) (q : ℕ)
    (hq : ∀ i, n i ≤ q) (Y : I → Type) (row : ∀ i, Fin (n i) → Y i)
    (agg : (∀ i, Fin (n i)) → ∀ i, Y i)
    (sep : ∀ v i, agg v i = row i (v i)) :
    (∀ i (a : Fin (n i)), a.val < q ∧
      agg (fun j => ⟨a.val % n j, Nat.mod_lt _ (hn j)⟩) i = row i a) ∧
    (∀ (m : ℕ) (schedule : Fin m → (i : I) → Fin (n i)),
      (∀ i, Function.Surjective (fun z => schedule z i)) → ∀ i, n i ≤ m) := by
  constructor
  · intro i a
    refine ⟨lt_of_lt_of_le a.isLt (hq i), ?_⟩
    rw [sep]
    congr 1
    apply Fin.ext
    exact Nat.mod_eq_of_lt a.isLt
  · intro m schedule hits i
    simpa using Fintype.card_le_of_surjective (fun z => schedule z i) (hits i)

import Mathlib.Data.Fintype.Card

theorem solution {blocks levels : ℕ} {α β : Type*}
    (f : (Fin blocks → α) → β) (select : Fin levels → Fin blocks)
    (decode : (Fin levels → α) → β)
    (heval : ∀ x, f x = decode (x ∘ select))
    (hdep : ∀ i, ∃ x y, (∀ j, j ≠ i → x j = y j) ∧ f x ≠ f y) :
    blocks ≤ levels := by
  have hs : Function.Surjective select := by
    intro i
    by_contra h
    obtain ⟨x, y, hagree, hdiff⟩ := hdep i
    apply hdiff
    rw [heval x, heval y]
    congr 1
    funext k
    exact hagree _ (fun hk ↦ h ⟨k, hk⟩)
  simpa using Fintype.card_le_of_surjective select hs

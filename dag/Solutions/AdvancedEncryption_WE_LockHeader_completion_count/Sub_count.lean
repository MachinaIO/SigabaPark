import Mathlib

theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (queried good₀ good₁ : Finset α)
    (miss : ∀ k, k ∉ queried → k ∈ good₀ → k ∉ good₁) :
    good₀.card + good₁.card ≤ Fintype.card α + queried.card := by
  have overlap : good₀ ∩ good₁ ⊆ queried := by
    intro k hk
    by_contra h
    obtain ⟨h₀, h₁⟩ := Finset.mem_inter.mp hk
    exact miss k h h₀ h₁
  rw [← Finset.card_union_add_card_inter]
  exact Nat.add_le_add (Finset.card_le_univ _) (Finset.card_le_card overlap)

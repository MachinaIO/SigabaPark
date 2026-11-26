import Lean

theorem solution {I C : Type} {A : I → Type}
    (valid kept : (i : I) → A i → Prop) (hits : (i : I) → A i → C → Prop)
    (sound : ∀ i a, kept i a → valid i a)
    (dom : ∀ i a, valid i a → ∃ b, kept i b ∧ ∀ c, hits i a c → hits i b c) :
    (∃ x : (i : I) → A i, (∀ i, valid i (x i)) ∧ ∀ c, ∃ i, hits i (x i) c) ↔
    (∃ y : (i : I) → A i, (∀ i, kept i (y i)) ∧ ∀ c, ∃ i, hits i (y i) c) := by
  classical
  constructor
  · rintro ⟨x, hx, hc⟩
    let y := fun i ↦ Classical.choose (dom i (x i) (hx i))
    refine ⟨y, fun i ↦ (Classical.choose_spec (dom i (x i) (hx i))).1, ?_⟩
    intro c
    obtain ⟨i, hi⟩ := hc c
    exact ⟨i, (Classical.choose_spec (dom i (x i) (hx i))).2 c hi⟩
  · rintro ⟨y, hy, hc⟩
    exact ⟨y, fun i ↦ sound i (y i) (hy i), hc⟩

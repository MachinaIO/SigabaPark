import Mathlib.Logic.Function.Basic

theorem solution {W Z : Type} (address : W → Z) :
    Function.Surjective address ↔
      ∀ test : Z → Prop, (∀ w, ¬test (address w)) → ∀ z, ¬test z := by
  constructor
  · intro hs test hn z
    obtain ⟨w, rfl⟩ := hs z
    exact hn w
  · intro h z
    classical
    by_contra missing
    have none : ∀ w, address w ≠ z := fun w e => missing ⟨w, e⟩
    exact h (fun u => u = z) none z rfl

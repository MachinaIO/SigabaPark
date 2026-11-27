import Mathlib

theorem solution {W R V P : Type*} (accept : W → Prop) (view : R → V)
    (cert : V → W → P) (key : R → Bool) :
    (∃ readKey : V → W → P → Bool,
      ∀ r w, accept w → readKey (view r) w (cert (view r) w) = key r) ↔
    (∀ r s, view r = view s → (∃ w, accept w) → key r = key s) := by
  classical
  constructor
  · rintro ⟨readKey, h⟩ r s e ⟨w, hw⟩
    rw [← h r w hw, ← h s w hw, e]
  · intro h
    refine ⟨fun v _ _ => if ex : ∃ r, view r = v then key (Classical.choose ex) else false, ?_⟩
    intro r w hw
    have ex : ∃ s, view s = view r := ⟨r, rfl⟩
    simp only [dif_pos ex]
    exact h _ _ (Classical.choose_spec ex) ⟨w, hw⟩

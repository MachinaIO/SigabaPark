import Mathlib

theorem solution {V E : Type*} (tail head : E → V) (live : E → Prop)
    (s t : V) (component : V → Bool) (hs : component s = false)
    (ht : component t = true)
    (hc : ∀ e, live e → component (tail e) = component (head e))
    (b : Bool) :
    ∃ F : (V → Bool) ≃ (V → Bool), ∀ p,
      F p s = p s ∧
      (Bool.xor (!b) (F p t)) = Bool.xor b (p t) ∧
      ∀ e, live e → Bool.xor (F p (tail e)) (F p (head e)) =
        Bool.xor (p (tail e)) (p (head e)) := by
  let flip := fun (p : V → Bool) v => Bool.xor (p v) (component v)
  have inv : Function.Involutive flip := by
    intro p
    funext v
    simp [flip]
  refine ⟨⟨flip, flip, inv, inv⟩, ?_⟩
  intro p
  change flip p s = p s ∧ Bool.xor (!b) (flip p t) = _ ∧ _
  refine ⟨by simp [flip, hs], ?_, ?_⟩
  · simp [flip, ht]
  · intro e he
    change Bool.xor (flip p (tail e)) (flip p (head e)) = _
    unfold flip
    rw [hc e he]
    cases component (head e) <;> simp

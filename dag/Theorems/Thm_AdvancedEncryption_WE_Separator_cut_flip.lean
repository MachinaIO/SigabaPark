import Mathlib

theorem AdvancedEncryption.WE.Separator.cut_flip {V E : Type*} (tail head : E → V) (live : E → Prop)
    (s t : V) (component : V → Bool) (hs : component s = false)
    (ht : component t = true)
    (hc : ∀ e, live e → component (tail e) = component (head e))
    (b : Bool) :
    ∃ F : (V → Bool) ≃ (V → Bool), ∀ p,
      F p s = p s ∧
      (Bool.xor (!b) (F p t)) = Bool.xor b (p t) ∧
      ∀ e, live e → Bool.xor (F p (tail e)) (F p (head e)) =
        Bool.xor (p (tail e)) (p (head e)) := by sorry

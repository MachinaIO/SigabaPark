import Definitions.Def_RectangleGrant
open RectangleGrant
theorem solution {V X E I : Type} (p : V → X → Prop) (s t : E → V)
    (edge : E → X → X → Prop) (l r : E → I → X → Prop)
    (h : ∀ e a b, edge e a b ↔ ∃ c, l e c a ∧ r e c b) :
    reaches p s t edge ↔ certified p s t l r := by
  classical
  constructor
  · rintro ⟨x,hx,he⟩
    have hh := fun e => (h e _ _).mp (he e)
    exact ⟨x,fun e => Classical.choose (hh e),hx,fun e => Classical.choose_spec (hh e)⟩
  · rintro ⟨x,c,hx,he⟩
    exact ⟨x,hx,fun e => (h e _ _).mpr ⟨c e,he e⟩⟩

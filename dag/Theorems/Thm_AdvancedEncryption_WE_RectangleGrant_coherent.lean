import Definitions.Def_RectangleGrant
open RectangleGrant
theorem AdvancedEncryption.WE.RectangleGrant.coherent {V X E I : Type} (p : V → X → Prop) (s t : E → V)
    (edge : E → X → X → Prop) (l r : E → I → X → Prop)
    (h : ∀ e a b, edge e a b ↔ ∃ c, l e c a ∧ r e c b) :
    reaches p s t edge ↔ certified p s t l r := by sorry

import Mathlib

namespace RectangleGrant

def reaches {V X E : Type} (p : V → X → Prop) (s t : E → V)
    (edge : E → X → X → Prop) : Prop :=
  ∃ x : V → X, (∀ v, p v (x v)) ∧ ∀ e, edge e (x (s e)) (x (t e))

def certified {V X E I : Type} (p : V → X → Prop) (s t : E → V)
    (l r : E → I → X → Prop) : Prop :=
  ∃ (x : V → X) (c : E → I), (∀ v, p v (x v)) ∧
    ∀ e, l e (c e) (x (s e)) ∧ r e (c e) (x (t e))


def masked (side pad common bit : Bool) : Bool :=
  Bool.xor pad (Bool.xor common (side && bit))



end RectangleGrant

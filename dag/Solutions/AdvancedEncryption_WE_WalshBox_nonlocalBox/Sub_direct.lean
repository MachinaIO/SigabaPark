import Definitions.Def_NandWalshBox
open NandWalshBox
theorem solution :
    (∀ h k x r : Bool, flip h k x (flip h k x r) = r) ∧
    ¬ ∃ f g : Bool → Bool, ∀ x y, (f x ^^ g y) = (x && y) := by
  constructor
  · decide
  · rintro ⟨f,g,h⟩
    have a := h false false
    have b := h false true
    have c := h true false
    have d := h true true
    cases f false <;> cases f true <;> cases g false <;> cases g true <;> simp_all

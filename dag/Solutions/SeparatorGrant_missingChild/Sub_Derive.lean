import Mathlib.Tactic

theorem solution {R P S I : Type*} (ok : R → Prop) (parent : R → P)
    (child : R → I → S) (live : I → S → Prop) (p : P)
    (dead : ¬ ∃ r, ok r ∧ parent r = p ∧ ∀ i, live i (child r i))
    (r : R) (hr : ok r) (hp : parent r = p) :
    ∃ i, ¬ live i (child r i) := by
  classical
  by_contra! h
  exact dead ⟨r, hr, hp, h⟩

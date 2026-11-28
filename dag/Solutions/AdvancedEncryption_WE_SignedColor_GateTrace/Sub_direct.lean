import Definitions.Def_SignedColorEnergy

open SignedColorEnergy

theorem solution (x : List Bool) (gs : SigabaNeo.GateList) :
    accepted (true :: x, true) gs ↔ SigabaNeo.evalGates (x,gs) = true := by
  have hg (a b z : Bool) : localOK a b z ↔ z = !(a && b) := by
    unfold localOK
    cases a <;> cases b <;> cases z <;> decide
  have aux (s : List Bool × Bool) : ∀ gates : SigabaNeo.GateList,
      accepted s gates ↔ (gates.foldl SigabaNeo.estep s).2 = true := by
    intro gates
    induction gates generalizing s with
    | nil => rfl
    | cons g gs ih =>
      obtain ⟨a,b⟩ := g
      simp [accepted, hg, ih, SigabaNeo.estep]
  exact aux (true :: x, true) gs

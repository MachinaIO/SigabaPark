import Definitions.Def_TwoTraceEnergy
import Mathlib.Tactic

private theorem corners2 : ∀ a b t u s : Bool,
    0 ≤ TwoTraceEnergy.localCost a b t b t ∧
    TwoTraceEnergy.localCost a b t b t ≤ TwoTraceEnergy.localCost a b t u s ∧
    TwoTraceEnergy.localCost a b t u s ≤ 6 ∧
    (TwoTraceEnergy.localCost a b t b t = 0 ↔ t = (a && b)) := by decide

private theorem inductionRun (gs : SigabaNeo.GateList) :
    (∀ l r p q, TwoTraceEnergy.zeroRun gs l r p q →
      (gs.foldl SigabaNeo.estep (l,p)).2 = true) ∧
    (∀ l p, (gs.foldl SigabaNeo.estep (l,p)).2 = true → TwoTraceEnergy.zeroRun gs l l p p) := by
  induction gs with
  | nil => exact ⟨fun _ _ _ _ h => h.1,fun _ _ h => ⟨h,h⟩⟩
  | cons g gs ih =>
    obtain ⟨i,j⟩ := g
    constructor
    · intro l r p q h
      obtain ⟨z,w,he,hr⟩ := h
      have h0 := corners2 (l.getD i true) (l.getD j true) (!z) (r.getD j true) (!w)
      have heq := h0.2.2.2.mp (le_antisymm (he ▸ h0.2.1) h0.1)
      have hz : z = !(l.getD i true && l.getD j true) := by
        simpa using congrArg Bool.not heq
      subst z
      exact ih.1 _ _ _ _ hr
    · intro l p h
      let z := !(l.getD i true && l.getD j true)
      refine ⟨z,z,?_,ih.2 _ _ h⟩
      exact (corners2 (l.getD i true) (l.getD j true) (!z) (l.getD j true) (!z)).2.2.2.mpr (by simp [z])

theorem solution (g : SigabaNeo.GateList) (x : List Bool) :
    (∃ y : List Bool, TwoTraceEnergy.zeroRun g (true :: x) (true :: y) true true) ↔
    SigabaNeo.evalGates (x,g) = true := by
  constructor
  · rintro ⟨y,hy⟩
    exact (inductionRun g).1 _ _ _ _ hy
  · intro hx
    exact ⟨x,(inductionRun g).2 _ _ hx⟩

import Mathlib.Logic.Function.Basic

theorem solution {S B Z : Type} [Inhabited Z] (producer : S → B) (target : S → Z) :
    (∃ h : B → Z, ∀ s, h (producer s) = target s) ↔
    (∀ s t, producer s = producer t → target s = target t) := by
  classical
  constructor
  · rintro ⟨h,hh⟩ s t e
    exact (hh s).symm.trans ((congrArg h e).trans (hh t))
  · intro stable
    let h := fun b => if ok : ∃ s, producer s = b then target (Classical.choose ok) else default
    refine ⟨h, fun s => ?_⟩
    have ok : ∃ t, producer t = producer s := ⟨s,rfl⟩
    simpa [h,ok] using stable (Classical.choose ok) s (Classical.choose_spec ok)

import Mathlib.Logic.Function.Basic

theorem AdvancedEncryption.WE.FusedRank.public_consumer {S B Z : Type} [Inhabited Z] (producer : S → B) (target : S → Z) :
    (∃ h : B → Z, ∀ s, h (producer s) = target s) ↔
    (∀ s t, producer s = producer t → target s = target t) := by
  sorry

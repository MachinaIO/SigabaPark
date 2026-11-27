import Definitions.Def_TerminalRectangle

open TerminalRectangle

theorem solution {m w : ℕ} (seed : Fin w → Bool) (rows : Fin m → Fin w → Bool) :
    ∃! pads : Fin m → Fin w → Bool, ∀ i t, (seed t ^^ pads i t) = rows i t := by
  refine ⟨fun i t => seed t ^^ rows i t, ?_, ?_⟩
  · intro i t
    change (seed t ^^ (seed t ^^ rows i t)) = rows i t
    cases hs : seed t <;> cases hr : rows i t <;> rfl
  · intro pads h
    funext i t
    have e := h i t
    cases hs : seed t <;> cases hp : pads i t <;> cases hr : rows i t <;> simp_all

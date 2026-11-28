import Definitions.Def_TableauShiftAudit

open GuardedIssuer

theorem AdvancedEncryption.WE.TableauAudit.miss_error {Q A : Type} (base o₀ o₁ valid : Q → Bool)
    (h₀ : ∀ q, valid q = false → o₀ q = base q)
    (h₁ : ∀ q, valid q = false → o₁ q = base q)
    (t : Tree Q A) (readBit : A → Bool) (miss : hit base valid t = false) :
    readBit (run o₀ t) = true ∨ readBit (run o₁ t) = false := by
  sorry

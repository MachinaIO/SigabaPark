import Mathlib
/-- Erasing a guarded pivot bit is a bijection on satisfying witnesses. -/
theorem AdvancedEncryption.WE.TranslationFrontend.guarded_pivot {W : Type*} (G : Bool → W → Prop) (q : Bool → W → Bool)
    (stable : ∀ y, G false y ↔ G true y)
    (toggle : ∀ y, G false y → q true y = !(q false y)) :
    ∃ E : {x : Bool × W // G x.1 x.2 ∧ q x.1 x.2 = false} ≃ {y // G false y},
      ∀ x, (E x).val = x.val.2 := by sorry

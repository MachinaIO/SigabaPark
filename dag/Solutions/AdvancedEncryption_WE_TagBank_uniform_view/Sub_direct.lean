import Mathlib
/-- Uniform label messages and uniform replacement bodies have a bijective joint public reparameterization. -/
theorem solution {L Y : Type*} [AddCommGroup L] [AddCommGroup Y] (offset : L) (mask : L → Y) :
    ∃ e : (L × Y) ≃ (L × Y), ∀ l y, e (l,y) = (l-offset,y+mask l) := by
  refine ⟨⟨fun v => (v.1-offset,v.2+mask v.1), fun v => (v.1+offset,v.2-mask (v.1+offset)), ?_, ?_⟩, ?_⟩
  · rintro ⟨l,y⟩
    simp
  · rintro ⟨l,y⟩
    simp
  · intro l y
    rfl

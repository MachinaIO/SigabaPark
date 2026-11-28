import Definitions.Def_NullSamplerCosts
open OneBitSampler
theorem solution {W Z : Type} (zero one : Z) (valid : W→Prop)
    (readBit : W→Z→Bool) (no : (¬∃ w, valid w) → zero=one)
    (yes : ∀ w, valid w → readBit w zero=false ∧ readBit w one=true) :
    (∃ w,valid w) ↔ zero≠one := by
  constructor
  · rintro ⟨w,hw⟩ e
    obtain ⟨a,b⟩:=yes w hw
    rw [e,b] at a
    contradiction
  · intro h
    by_contra hn
    exact h (no hn)

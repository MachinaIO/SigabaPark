import Definitions.Def_NullSamplerCosts
open OneBitSampler
theorem AdvancedEncryption.WE.NullSampler.observableCompression {W Z : Type} (zero one : Z) (valid : W→Prop)
    (readBit : W→Z→Bool) (no : (¬∃ w, valid w) → zero=one)
    (yes : ∀ w, valid w → readBit w zero=false ∧ readBit w one=true) :
    (∃ w,valid w) ↔ zero≠one := by sorry

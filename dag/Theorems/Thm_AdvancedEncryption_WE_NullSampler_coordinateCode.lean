import Definitions.Def_NullSamplerCosts
open OneBitSampler
theorem AdvancedEncryption.WE.NullSampler.coordinateCode (n k : Nat) (enc : (Fin n→Bool) → Fin (2^k))
    (dec : Fin (2^k) → Fin n→Bool) :
    2^n ≤ 2^k + ∑ x : Fin n→Bool, ∑ i : Fin n, if dec (enc x) i=x i then 0 else 1 := by sorry

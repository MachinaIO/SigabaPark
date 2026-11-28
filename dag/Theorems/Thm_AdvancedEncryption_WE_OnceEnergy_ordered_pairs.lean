import Definitions.Def_WE_OnceTraceScan
open AdvancedEncryption.WE.OnceScan
/-- A one-pass horizontal accumulator produces the ordered quadratic cross terms. -/
theorem AdvancedEncryption.WE.OnceEnergy.ordered_pairs {H K : Type*} [AddCommMonoid H] [AddCommMonoid K]
    (dot : H → H → K) (right0 : ∀ a, dot a 0 = 0)
    (leftAdd : ∀ a b c, dot (a+b) c = dot a c+dot b c)
    (rightAdd : ∀ a b c, dot a (b+c) = dot a b+dot a c)
    (rows : List (H × H × K)) (start : H) :
    stream dot start rows = dot start (later rows)+pairs dot rows := by sorry

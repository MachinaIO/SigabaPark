import Definitions.Def_WE_OnceTraceScan
open AdvancedEncryption.WE.OnceScan
/-- A one-pass horizontal accumulator produces the ordered quadratic cross terms. -/
theorem solution {H K : Type*} [AddCommMonoid H] [AddCommMonoid K]
    (dot : H → H → K) (right0 : ∀ a, dot a 0 = 0)
    (leftAdd : ∀ a b c, dot (a+b) c = dot a c+dot b c)
    (rightAdd : ∀ a b c, dot a (b+c) = dot a b+dot a c)
    (rows : List (H × H × K)) (start : H) :
    stream dot start rows = dot start (later rows)+pairs dot rows := by
  induction rows generalizing start with
  | nil => simp [stream,later,pairs,right0]
  | cons r rs ih =>
    obtain ⟨a,b,c⟩ := r
    simp only [stream,later,pairs,ih,leftAdd,rightAdd]
    ac_rfl

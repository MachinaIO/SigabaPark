import Definitions.Def_NullSamplerCosts
open OneBitSampler
theorem AdvancedEncryption.WE.NullSampler.sparseQueries {I S X : Type} [Fintype I] [Fintype S] [DecidableEq I]
    (T : Bool → S → Tree I X) (D : I → X → Bool) (margin : ℤ)
    (hgap : ∀ v, margin ≤ ∑ s,
      ((accept (T true s) (spike v) (D v)-accept (T false s) (spike v) (D v))-
       (accept (T true s) (fun _=>false) (D v)-accept (T false s) (fun _=>false) (D v)))) :
    (Fintype.card I:ℤ)*margin ≤
      ∑ s, ((visited (T true s)).card+(visited (T false s)).card:ℤ) := by sorry

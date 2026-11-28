import Mathlib

theorem AdvancedEncryption.WE.FactoredRow.IsolatePoint {Z I K : Type*} [Fintype I] [DecidableEq Z] [Zero K]
    (key : Z → I → Bool) (inj : Function.Injective key)
    (V : (Z → K) → Prop)
    (step : ∀ (i : I) (b : Bool) (f : Z → K), V f →
      V (fun z => if key z i = b then f z else 0))
    (a : Z) (f : Z → K) (hf : V f) :
    V (fun z => if z = a then f z else 0) := by sorry

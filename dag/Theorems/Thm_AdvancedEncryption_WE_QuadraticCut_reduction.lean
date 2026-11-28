import Definitions.Def_QuadraticNandCut
open AffineNandCut
open scoped BigOperators
theorem AdvancedEncryption.WE.QuadraticCut.reduction {X V L R : Type*} [AddCommGroup V] [AddCommGroup L] [AddCommGroup R]
    (e : V≃+L×R) (a h : X→V) (q : X→R) (b : V) (hh : ∀ x, e (h x)=(0,q x)) (x : X) :
    a x+h x=b ↔ (e (b-a x)).1=0 ∧ (e (b-a x)).2=q x := by sorry

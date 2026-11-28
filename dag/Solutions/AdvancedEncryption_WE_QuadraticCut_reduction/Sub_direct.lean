import Definitions.Def_QuadraticNandCut
open AffineNandCut
open scoped BigOperators
theorem solution {X V L R : Type*} [AddCommGroup V] [AddCommGroup L] [AddCommGroup R]
    (e : V≃+L×R) (a h : X→V) (q : X→R) (b : V) (hh : ∀ x, e (h x)=(0,q x)) (x : X) :
    a x+h x=b ↔ (e (b-a x)).1=0 ∧ (e (b-a x)).2=q x := by
  have eq : a x+h x=b ↔ b-a x=h x := by rw [sub_eq_iff_eq_add]; constructor <;> intro z <;> simpa [add_comm] using z.symm
  rw [eq,← e.injective.eq_iff, hh]
  exact Prod.ext_iff

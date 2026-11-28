import Definitions.Def_LinearObservationJoin
open ObservationJoin
theorem solution {E A B C : Type*} (a : E→A) (b : E→B) (key : E→C)
    (merge : ∀ x y,key x=key y→∃ w,a w=a x ∧ b w=b y) (P : A→Prop) (Q : B→Prop) :
    (∃ w,P (a w) ∧ Q (b w)) ↔
    ∃ c,(∃ x,key x=c ∧ P (a x)) ∧ (∃ y,key y=c ∧ Q (b y)) := by
  constructor
  · rintro ⟨w,p,q⟩;exact ⟨key w,⟨w,rfl,p⟩,w,rfl,q⟩
  · rintro ⟨c,⟨x,h,p⟩,y,g,q⟩
    obtain ⟨w,wa,wb⟩:=merge x y (h.trans g.symm)
    exact ⟨w,wa ▸ p,wb ▸ q⟩

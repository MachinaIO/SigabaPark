import Definitions.Def_LinearObservationJoin
open ObservationJoin
theorem solution {K E A B : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (L : E→ₗ[K]A) (R : E→ₗ[K]B) (V : Submodule K E) (x y : E) :
    x-y∈fibre L R V ↔ ∃ z, L z=L x ∧ R z=R y ∧ x-z∈V ∧ z-y∈V := by
  rw [fibre,Submodule.mem_sup]
  constructor
  · rintro ⟨a,ha,b,hb,h⟩
    obtain ⟨la,va⟩:=ha
    obtain ⟨rb,vb⟩:=hb
    change L a=0 at la
    change R b=0 at rb
    have hx : x-a=y+b := by rw [←sub_eq_zero]; have hh:=congrArg (fun t => t-a-b) h; abel_nf at hh ⊢; exact hh.symm
    refine ⟨x-a,by simp [la],?_,?_,?_⟩
    · rw [hx,map_add,rb,add_zero]
    · simpa using va
    · rw [hx]; simpa using vb
  · rintro ⟨z,hl,hr,hx,hy⟩
    exact ⟨x-z,⟨by simp [LinearMap.mem_ker,hl],hx⟩,z-y,⟨by simp [LinearMap.mem_ker,hr],hy⟩,by abel⟩

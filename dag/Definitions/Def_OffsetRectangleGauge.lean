import SigabaNeoStd.Lattices.RingLWEInst
import Mathlib.Tactic
namespace OffsetRectangleGauge
open Cslib.Probability
variable {U G : Type} [AddCommGroup U] [Fintype U] [AddCommGroup G]

theorem coset (f : U →+ G) (r : G) :
    (Cslib.Probability.PMF.uniformOfFintype U).map (fun u ↦ r+f u)=
    (Cslib.Probability.PMF.uniformOfFintype U).map f ↔ ∃ v,f v=r := by
  constructor
  · intro he
    have h : r∈((Cslib.Probability.PMF.uniformOfFintype U).map (fun u ↦ r+f u)).support := by
      rw [PMF.support_map]; exact ⟨0,PMF.mem_support_uniformOfFintype _,by simp⟩
    rw [he,PMF.support_map] at h
    obtain ⟨u,_,h⟩ := h; exact ⟨u,h⟩
  · rintro ⟨v,rfl⟩
    have he := congrArg (PMF.map f)
      (Cslib.Probability.PMF.uniformOfFintype_map_equiv (Equiv.addLeft v))
    simpa only [PMF.map_comp,Function.comp_def,Equiv.coe_addLeft,map_add] using he

abbrev F := ZMod 2
variable {P Q E : Type}
abbrev Coins (P Q : Type) := (P → F) × (Q → F) × (P × Q → F)
def entries (p : E → P) (q : E → Q) (mark : P × Q → Bool) : Coins P Q →+ (E → F) where
  toFun k e := k.1 (p e)+k.2.1 (q e)+(if mark (p e,q e) then k.2.2 (p e,q e) else 0)
  map_zero' := by funext e; simp
  map_add' a b := by funext e; cases h : mark (p e,q e) <;> simp [h] <;> abel

theorem feedback (p : E → P) (q : E → Q) (mark : P × Q → Bool)
    (role : E → F) (color : P × Q → F) (well : ∀ e,color (p e,q e)=role e)
    (l : P → F) (r : Q → F)
    (tree : ∀ e,mark (p e,q e)=false → l (p e)+r (q e)=role e) :
    ∃ k,entries p q mark k=role := by
  refine ⟨(l,r,fun a ↦ color a-l a.1-r a.2),?_⟩
  funext e; cases h : mark (p e,q e)
  · simpa [entries,h] using tree e h
  · simp [entries,h,well]

theorem rectangle (l r : Bool → F) :
    (l false+r false)-(l false+r true)+(l true+r true)-(l true+r false)=0 := by abel
theorem odd_impossible (l r : Bool → F)
    (a : l false+r false=0) (b : l false+r true=0) (c : l true+r false=0) :
    l true+r true≠1 := by
  intro d; have h := rectangle l r; rw [a,b,c,d] at h; norm_num at h
end OffsetRectangleGauge

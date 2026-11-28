import SigabaNeoStd.Lattices.RingLWEInst
import Mathlib.Tactic
namespace WholeViewRoutes
open Cslib.Probability

variable {J C : Type}
inductive Route (J : Type)
  | leaf (j : J) | both (x y : Route J) | either (x y : Route J)
def truth (ok : J → Bool) : Route J → Bool
  | .leaf j => ok j | .both x y => truth ok x && truth ok y
  | .either x y => truth ok x || truth ok y

noncomputable def join (a b : PMF (List C)) :=
  a.bind fun x ↦ b.map fun y ↦ x++y
noncomputable def fair := Cslib.Probability.PMF.uniformOfFintype Bool
noncomputable def enc (leaf : J → Bool → PMF C) : Route J → Bool → PMF (List C)
  | .leaf j,b => (leaf j b).map fun c ↦ [c]
  | .either x y,b => join (enc leaf x b) (enc leaf y b)
  | .both x y,b => fair.bind fun r ↦ join (enc leaf x r) (enc leaf y (b ^^ r))

def flip : Bool ≃ Bool := ⟨not,not,Bool.not_not,Bool.not_not⟩
theorem switch {O : Type} (f : Bool → PMF O) : fair.bind (fun r ↦ f (!r))=fair.bind f := by
  have hh := congrArg (fun p : PMF Bool ↦ p.bind f) (Cslib.Probability.PMF.uniformOfFintype_map_equiv flip)
  rw [PMF.bind_map] at hh
  exact hh

theorem complete_no (leaf : J → Bool → PMF C) (ok : J → Bool)
    (hp : ∀ j,ok j=false → leaf j false=leaf j true)
    (p : Route J) (h : truth ok p=false) : enc leaf p false=enc leaf p true := by
  induction p with
  | leaf j => simp only [enc,hp j h]
  | either x y ix iy =>
    change (truth ok x || truth ok y)=false at h
    have hx : truth ok x=false := by cases h₁ : truth ok x <;> simp_all
    have hy : truth ok y=false := by cases h₂ : truth ok y <;> simp_all
    simp only [enc,ix hx,iy hy]
  | both x y ix iy =>
    change (truth ok x && truth ok y)=false at h
    by_cases hx : truth ok x=false
    · have same (r : Bool) : enc leaf x r=enc leaf x false := by cases r <;> simp [ix hx]
      change fair.bind (fun r ↦ join (enc leaf x r) (enc leaf y (false ^^ r)))=_
      simp only [enc,Bool.false_xor,Bool.true_xor,same]
      exact (switch (fun r ↦ join (enc leaf x false) (enc leaf y r))).symm
    · have hy : truth ok y=false := by cases h₁ : truth ok x <;> simp_all
      have same (r : Bool) : enc leaf y r=enc leaf y false := by cases r <;> simp [iy hy]
      simp only [enc,same]

/-- Exact subgroup criterion for entire representative-independent encodings. -/
theorem subgroup {H G : Type} [CommGroup H] [Fintype H] [CommGroup G]
    (f : H →* G) (γ : G) :
    (Cslib.Probability.PMF.uniformOfFintype H).map (fun u ↦ γ*f u)=
    (Cslib.Probability.PMF.uniformOfFintype H).map f ↔ ∃ v,f v=γ := by
  classical
  constructor
  · intro he
    have h : γ∈((Cslib.Probability.PMF.uniformOfFintype H).map (fun u ↦ γ*f u)).support := by
      rw [PMF.support_map]; exact ⟨1,PMF.mem_support_uniformOfFintype _,by simp⟩
    rw [he,PMF.support_map] at h
    obtain ⟨v,_,hv⟩ := h
    exact ⟨v,hv⟩
  · rintro ⟨v,rfl⟩
    have he := congrArg (PMF.map f) (Cslib.Probability.PMF.uniformOfFintype_map_equiv (Equiv.mulLeft v))
    simpa only [PMF.map_comp,Function.comp_def,Equiv.coe_mulLeft,map_mul] using he
end WholeViewRoutes

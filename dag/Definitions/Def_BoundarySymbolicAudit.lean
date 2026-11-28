import SigabaNeoStd.Lattices.RingLWEInst
import Mathlib.Tactic

namespace BoundarySymbolicAudit
open Cslib.Probability

section Masks
variable {K C : Type} [AddCommGroup K] [Fintype K] [AddCommGroup C]
noncomputable def phaseLaw (f : K →+ C) (d : C) : PMF C :=
  (PMF.uniformOfFintype K).map fun x ↦ f x+d

/-- For all visible terminal coordinates together, the message offset must
lie in the image of the live affine pad map, and this condition suffices. -/
theorem phase_iff (f : K →+ C) (d : C) :
    phaseLaw f d=phaseLaw f 0 ↔ ∃ v, f v=d := by
  classical
  constructor
  · intro h
    have hd : d ∈ (phaseLaw f d).support := by
      rw [phaseLaw,PMF.support_map]
      exact ⟨0,PMF.mem_support_uniformOfFintype _,by simp⟩
    rw [h] at hd
    rw [phaseLaw,PMF.support_map] at hd
    obtain ⟨v,_,hv⟩ := hd
    exact ⟨v,by simpa using hv⟩
  · rintro ⟨v,rfl⟩
    have hu := PMF.uniformOfFintype_map_equiv (Equiv.addRight v)
    simpa [phaseLaw,PMF.map_comp,Function.comp_def] using congrArg (PMF.map f) hu

/-- Additional metadata may depend on the private masks if it is invariant
under the same translation. Postprocessing both arguments preserves equality. -/
theorem side_view {Z O : Type} (f : K →+ C) (v : K) (side : K → Z)
    (inv : ∀ x,side (x+v)=side x) (finish : Z → C → O) :
    (PMF.uniformOfFintype K).map (fun x ↦ finish (side x) (f x+f v)) =
    (PMF.uniformOfFintype K).map (fun x ↦ finish (side x) (f x)) := by
  have h := PMF.uniformOfFintype_map_equiv (Equiv.addRight v)
  simpa [PMF.map_comp,Function.comp_def,inv] using
    congrArg (PMF.map (fun x ↦ finish (side x) (f x))) h
end Masks

section Graph
variable {V C : Type}
inductive Reach (edge : V → V → Prop) (root : V → Prop) : V → Prop
  | start {v} : root v → Reach edge root v
  | next {u v} : Reach edge root u → edge u v → Reach edge root v

theorem contained {edge : V → V → Prop} {root live : V → Prop}
    (roots : ∀ v,root v → live v) (closed : ∀ u v,live u → edge u v → live v)
    {v : V} (h : Reach edge root v) : live v := by
  induction h with
  | start h => exact roots _ h
  | next _ he ih => exact closed _ _ ih he

/-- Two closure certificates that separate typed terminal classes exist
exactly when the classes of actually graph-reachable terminals separate. -/
theorem separating_cover (e₁ e₂ : V → V → Prop) (r₁ r₂ : V → Prop)
    (t₁ t₂ : V → C → Prop) :
    (∃ l₁ l₂ : V → Prop, (∀ v,r₁ v → l₁ v) ∧ (∀ v,r₂ v → l₂ v) ∧
      (∀ u v,l₁ u → e₁ u v → l₁ v) ∧ (∀ u v,l₂ u → e₂ u v → l₂ v) ∧
      ∀ u v c,l₁ u → l₂ v → t₁ u c → t₂ v c → False) ↔
    ∀ u v c,Reach e₁ r₁ u → Reach e₂ r₂ v → t₁ u c → t₂ v c → False := by
  constructor
  · rintro ⟨l₁,l₂,hr₁,hr₂,hc₁,hc₂,hs⟩ u v c hu hv
    exact hs u v c (contained hr₁ hc₁ hu) (contained hr₂ hc₂ hv)
  · intro h
    exact ⟨Reach e₁ r₁,Reach e₂ r₂,fun _ ↦ Reach.start,fun _ ↦ Reach.start,
      fun _ _ ↦ Reach.next,fun _ _ ↦ Reach.next,h⟩
end Graph
end BoundarySymbolicAudit

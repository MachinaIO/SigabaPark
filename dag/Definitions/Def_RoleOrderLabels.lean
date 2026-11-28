import Mathlib.Tactic
namespace RoleOrderLabels

/-- First unequal bit position with the right bit; used on equal-width words. -/
def first : List Bool → List Bool → Option (ℕ × Bool)
  | x::xs, y::ys => if x=y then (first xs ys).map (fun p => (p.1+1,p.2)) else some (0,y)
  | _, _ => none

/-- Payload-absorbing relabeling of masks at right-reachable colors. -/
noncomputable def rekey {C G : Type*} [AddCommGroup G] (R : Set C) (b : G) :
    (C → G) ≃ (C → G) := by
  classical
  exact Equiv.addRight (fun c => if c ∈ R then b else 0)

end RoleOrderLabels

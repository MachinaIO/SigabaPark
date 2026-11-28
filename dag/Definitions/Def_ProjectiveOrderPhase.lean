import Mathlib.Tactic
namespace ProjectiveOrderPhase
variable {R : Type} [CommRing R]
structure H (R : Type) where
  x : R
  y : R
  z : R
  deriving DecidableEq
def op (a b : H R) : H R := ⟨a.x+b.x,a.y+b.y,a.z+b.z+a.x*b.y⟩
def central (t : R) (a : H R) : H R := ⟨a.x,a.y,t+a.z⟩
def correction (a b : H R) := a.x*b.y-b.x*a.y
theorem assoc (a b c : H R) : op (op a b) c=op a (op b c) := by cases a; cases b; cases c; simp [op]; ring_nf <;> simp
theorem adj (a b : H R) : op a b=central (correction a b) (op b a) := by
  cases a; cases b; simp [op,central,correction]; ring_nf <;> simp
def fold : List (H R) → H R
  | [] => ⟨0,0,0⟩
  | a::l => op a (fold l)
def pairs : List (H R) → R
  | [] => 0
  | a::l => a.x*(l.map H.y).sum+pairs l
theorem normal (l : List (H R)) :
    fold l=⟨(l.map H.x).sum,(l.map H.y).sum,(l.map H.z).sum+pairs l⟩ := by
  induction l with
  | nil => simp [fold,pairs]
  | cons a l ih => simp [fold,ih,pairs,op]; ring_nf <;> simp
theorem reorder {a b : List (H R)} (p : a.Perm b) :
    fold a=central (pairs a-pairs b) (fold b) := by
  rw [normal,normal]
  have hx := (p.map H.x).sum_eq; have hy := (p.map H.y).sum_eq; have hz := (p.map H.z).sum_eq
  rw [hx,hy,hz]; simp [central]; ring_nf <;> simp
end ProjectiveOrderPhase

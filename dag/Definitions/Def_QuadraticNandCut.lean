import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
open scoped BigOperators
namespace AffineNandCut
def sgn (b : Bool) : ℤ := if b then -1 else 1
def chars {X : Type*} : List (X→Bool) → List (X→ℤ)
  | [] => [fun _ => 1]
  | q::qs => let ts:=chars qs; ts ++ ts.map (fun t x => sgn (q x)*t x)
theorem mapMul (c : ℤ) (l : List ℤ) : (l.map (c*·)).sum = c*l.sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih,mul_add]
theorem orth {X : Type*} (qs : List (X→Bool)) (x : X) :
    ((chars qs).map (· x)).sum = if qs.all (fun q => !(q x)) then 2^qs.length else 0 := by
  induction qs with
  | nil => simp [chars]
  | cons q qs ih =>
    simp only [chars,List.map_append,List.sum_append,List.map_map,List.all_cons,List.length_cons]
    have h : ((chars qs).map ((fun b => sgn (q x)*b) ∘ (fun t => t x))).sum =
        sgn (q x)*((chars qs).map (· x)).sum := by
      rw [←List.map_map,mapMul]
    change ((chars qs).map (· x)).sum + ((chars qs).map ((fun b => sgn (q x)*b) ∘ (fun t => t x))).sum = _
    rw [h,ih]
    have hb (v t : Bool) (k : ℕ) :
        (if t then (2:ℤ)^k else 0)+sgn v*(if t then (2:ℤ)^k else 0) =
        (if (!v && t) then (2:ℤ)^(k+1) else 0) := by
      cases v <;> cases t <;> simp [sgn,pow_succ] <;> ring
    exact hb _ _ _
theorem interchange {X : Type*} [Fintype X] (ts : List (X→ℤ)) :
    (ts.map (fun t => ∑ x,t x)).sum = ∑ x,(ts.map (· x)).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih,Finset.sum_add_distrib]
end AffineNandCut
open AffineNandCut

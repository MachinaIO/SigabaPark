import Mathlib

namespace CoherentCheckerExpansion

variable {R : Type} [Ring R]

def zeros : List (R × R) → R
  | [] => 1
  | x :: xs => x.1 * zeros xs

def actual : List (R × R) → R
  | [] => 1
  | x :: xs => (x.1 + x.2) * actual xs

def mixed : List (R × R) → List R
  | [] => []
  | x :: xs => (x.2 * zeros xs) :: (mixed xs).map (fun a => (x.1+x.2)*a)

def singles : List (R × R) → List R
  | [] => []
  | x :: xs => (x.2 * zeros xs) :: (singles xs).map (fun a => x.1*a)

def pairs : List (R × R) → List R
  | [] => []
  | x :: xs => (mixed xs).map (fun a => x.2*a) ++ (pairs xs).map (fun a => x.1*a)

theorem sum_left (r : R) (l : List R) : (l.map (fun a => r*a)).sum = r*l.sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih,mul_add]

theorem mixed_sum (l : List (R × R)) : (mixed l).sum = actual l - zeros l := by
  induction l with
  | nil => simp [mixed,actual,zeros]
  | cons x l ih =>
    simp only [mixed,List.sum_cons,sum_left,ih,actual,zeros]
    noncomm_ring

theorem mixed_count (l : List (R × R)) : (mixed l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [mixed,ih]

end CoherentCheckerExpansion

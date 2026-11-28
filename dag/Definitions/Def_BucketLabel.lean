import Mathlib

namespace BucketLabel

def release {R I T : Type} [Ring R] {V : Type} [AddCommGroup V] [Module R V]
    (key : I → T) (row : I → V →ₗ[R] R) (target : I → R)
    (r : T → V) (b : R) (i : I) : R := row i (r (key i)) + target i * b



def good (a d c : Nat) : Bool :=
  let z := (a*d+c)%16
  decide (z ≤ 2 ∨ 14 ≤ z)





end BucketLabel

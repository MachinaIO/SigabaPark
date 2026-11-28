import Mathlib

theorem solution {R : Type*} [CommRing R] (a x y z u : R) (h : a^4+1=0) :
    let p := x+a*y+a^2*z+a^3*u
    let r := x+a^3*y-a^2*z+a*u
    let n := x-a*y+a^2*z-a^3*u
    let s := x-a^3*y-a^2*z-a*u
    p+r+n+s=4*x ∧ -a^3*(p-n)-a*(r-s)=4*y ∧
    -a^2*(p+n-r-s)=4*z ∧ -a*(p-n)-a^3*(r-s)=4*u := by
  dsimp only
  refine ⟨by ring, ?_, ?_, ?_⟩
  · linear_combination (-4*y-2*a^2*u)*h
  · linear_combination (-4*z)*h
  · linear_combination (-2*a^2*y-4*u)*h

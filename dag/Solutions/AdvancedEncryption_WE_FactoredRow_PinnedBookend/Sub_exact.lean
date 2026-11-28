import Mathlib

theorem solution {R : Type*} [CommRing R] (head tail phase noise flood : R) (on : Bool) :
    ((head+(if on then 1 else 0))*phase+tail+noise)-(head*phase+tail+flood) =
    (if on then phase else 0)+noise-flood := by
  cases on <;> simp <;> ring

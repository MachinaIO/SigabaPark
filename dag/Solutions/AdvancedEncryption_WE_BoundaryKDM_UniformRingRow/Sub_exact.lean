import Mathlib

theorem solution {R : Type*} [CommRing R] (alpha s tu tv d e : R) :
    (alpha*s+e)+(alpha-d)*tu+d*tv = (alpha-d)*(s+tu)+e+d*(s+tv) := by
  ring

import Mathlib

theorem solution {R : Type*} [CommRing R] (d B p s m ed ef er : R) :
    (d*s + ed + m) - (p*((B*s)+ef) + d*s - (p*(B*s)+er)) =
      m + ed - p*ef + er := by
  ring

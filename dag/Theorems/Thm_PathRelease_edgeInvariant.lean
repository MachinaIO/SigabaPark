import Definitions.Def_PathRelease
import Mathlib.Tactic

theorem PathRelease.edgeInvariant {K : Type*} [CommRing K] (a y r h : K) :
    (y+a*h)-a*(r+h) = y-a*r := by
  sorry

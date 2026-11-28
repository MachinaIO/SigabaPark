import Definitions.Def_PathRelease
import Mathlib.Tactic

theorem PathRelease.localRead {V K : Type*} [AddCommGroup V] [AddCommGroup K]
    (g : V →+ K) (r c : V) (h : g r=0) :
    g (r+c)=g c := by
  sorry

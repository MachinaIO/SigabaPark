import Definitions.Def_PathRelease
import Mathlib.Tactic

theorem solution {V K : Type*} [AddCommGroup V] [AddCommGroup K]
    (g : V →+ K) (r c : V) (h : g r=0) :
    g (r+c)=g c := by
  rw [map_add,h,zero_add]

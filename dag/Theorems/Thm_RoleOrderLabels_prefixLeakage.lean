import Definitions.Def_RoleOrderLabels
import Mathlib.Tactic

theorem RoleOrderLabels.prefixLeakage (x y u v : List Bool) (hs : x.length = y.length) (hd : x ≠ y) :
    RoleOrderLabels.first (x ++ u) (y ++ v) = RoleOrderLabels.first x y := by
  sorry

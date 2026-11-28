import Definitions.Def_RoleOrderLabels
import Mathlib.Tactic

theorem solution (x y u v : List Bool) (hs : x.length = y.length) (hd : x ≠ y) :
    RoleOrderLabels.first (x ++ u) (y ++ v) = RoleOrderLabels.first x y := by
  induction x generalizing y with
  | nil =>
    cases y <;> simp_all
  | cons x xs ih =>
    cases y with
    | nil => simp at hs
    | cons y ys =>
      by_cases h : x=y
      · subst y
        have hl : xs.length = ys.length := by simpa using hs
        have hn : xs ≠ ys := by intro he; exact hd (he ▸ rfl)
        simp [RoleOrderLabels.first, ih ys hl hn]
      · simp [RoleOrderLabels.first,h]

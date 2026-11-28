import Definitions.Def_PathRelease
import Mathlib.Tactic

theorem solution {K : Type*} [Field K] (a shift x : K) (ha : a ≠ 0) :
    a * (x - shift / a) + shift = a*x := by
  field_simp
  <;> ring

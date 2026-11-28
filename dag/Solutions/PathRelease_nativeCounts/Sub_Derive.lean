import Definitions.Def_PathRelease
import Mathlib.Tactic

theorem solution : 1+128+128*127/2=8257 ∧ 2^127< (2^129 : ℕ) ∧
    128^15 * 2^135 = (65536:ℕ)^15 := by
  norm_num

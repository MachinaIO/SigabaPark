import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

theorem solution : 128 + 2*(128-1) + 3714 = 4096 ∧ (2^64:ℕ)^2=2^128 := by
  norm_num

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

theorem AdvancedEncryption.WE.FEPacking.joint_native_floor (a b : ℕ) (m : List ℕ) (total : a + m.sum + b = 128) :
    2^32 ≤ 65536 * ((a :: m).zipWith (fun x y => 2^(x+y)) (m ++ [b])).sum +
      1024 * (2^(m.length + 1) - 2) := by
  sorry

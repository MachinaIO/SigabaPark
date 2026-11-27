import Mathlib

theorem AdvancedEncryption.WE.BKSStar.fixed_bit_normalization (u v common : ℝ) :
    |(1 - u + common) / 2 - (1 - v + common) / 2| =
      |(1 - u + v) / 2 - 1 / 2| ∧
    |(1 - u + v) / 2 - 1 / 2| = |v - u| / 2 := by sorry

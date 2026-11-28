import Definitions.Def_FixedTargetGeometry
open FixedTarget225
theorem AdvancedEncryption.WE.FixedTarget.scaledMajority (a : ℕ → ℝ) (n : ℕ) (ha : ∀ j, 0≤a j)
    (s x : ℝ) (h0 : 0≤s) (h1 : s≤1) (x0 : 0≤x) (x1 : x≤1) :
    s*majSeries a n x ≤ majSeries a n (s*x) := by sorry

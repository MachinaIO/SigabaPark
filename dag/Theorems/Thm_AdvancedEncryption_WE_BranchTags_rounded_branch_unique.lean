import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Int

theorem AdvancedEncryption.WE.BranchTags.rounded_branch_unique
    (q p tolerance d d' t t' : ℤ) (hq : 0 < q) (hsep : 2 * tolerance < q)
    (h₀ : |p * d - q * t| ≤ tolerance) (h₁ : |p * d' - q * t'| ≤ tolerance)
    (hsame : q ∣ d - d') (hrange : |t - t'| < p) : t = t' := by sorry

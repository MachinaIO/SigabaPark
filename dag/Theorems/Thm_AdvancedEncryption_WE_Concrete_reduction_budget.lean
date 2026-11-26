import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-- Concrete hybrid budget with reduction overhead (note `pq-we-new-directions`). An adversary of
cost `c ≥ 1` and advantage `adv ≤ Σ_{i<L} ε i`, where each hop `i` is turned by a reduction of
additive overhead `T` into an attacker on a premise of strength `P` (`2^P ε_i² ≤ c + T`), satisfies
`2^P adv² ≤ L² (1 + T) c`: false-statement security of `P − 2 log₂ L − log₂(1 + T)` bits. -/
theorem AdvancedEncryption.WE.Concrete.reduction_budget (L P : ℕ) (ε : ℕ → ℝ)
    (adv c T : ℝ) (hc : 1 ≤ c) (hT : 0 ≤ T) (hadv0 : 0 ≤ adv)
    (hadv : adv ≤ ∑ i ∈ Finset.range L, ε i)
    (hhop : ∀ i < L, (2 : ℝ) ^ P * ε i ^ 2 ≤ c + T) :
    (2 : ℝ) ^ P * adv ^ 2 ≤ (L : ℝ) ^ 2 * (1 + T) * c := by sorry

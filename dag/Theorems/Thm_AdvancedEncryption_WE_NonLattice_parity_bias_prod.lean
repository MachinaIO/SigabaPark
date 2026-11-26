import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-- Piling-up identity (exact, any finite index type). For `x` with independent Bernoulli(`τ`) coordinates in `F_2`, the bias `E[(-1)^{⟨c, x⟩}]` of any parity equals the product over coordinates of `1` (if `c_i = 0`) or `1 - 2τ` (if `c_i ≠ 0`), i.e. `(1 - 2τ)^{wt c}`. Base case of the noise-compounding analysis of Hamming-metric GGH15 analogues in the note `pq-we-non-lattice-ggh15-analogues`. -/
theorem AdvancedEncryption.WE.NonLattice.parity_bias_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ℝ) (c : ι → ZMod 2) :
    ∑ x : ι → ZMod 2, (∏ i, (if x i = 1 then τ else 1 - τ)) * (-1 : ℝ) ^ (∑ i, c i * x i).val
      = ∏ i, (if c i = 0 then (1 : ℝ) else 1 - 2 * τ) := by sorry

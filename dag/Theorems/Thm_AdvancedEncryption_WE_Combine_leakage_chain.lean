import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-- **Leakage chain (note `pq-we-hybrid-tool-combinations`, §7).** Read `f i` as the best prediction probability of the key in hybrid `i`. A hop that leaks `ℓ` bits (`K = 2^ℓ`) plus a computational loss `ε` compounds multiplicatively: over `T` witness-indexed hops the bound is `2^{ℓT}`. With `T ≈ 2^{128}` and a key of `k` bits, a search (unpredictability) relaxation tolerates only `ℓ ≤ (k − λ)/T` bits per hop, which is below one bit for any key of size `≤ 2^{100}`. -/
theorem AdvancedEncryption.WE.Combine.leakage_chain (f : ℕ → ℝ) (K ε : ℝ) (hK : 0 ≤ K) (T : ℕ)
    (hhop : ∀ i < T, f i ≤ K * f (i + 1) + ε) :
    f 0 ≤ K ^ T * f T + ε * ∑ i ∈ Finset.range T, K ^ i := by sorry

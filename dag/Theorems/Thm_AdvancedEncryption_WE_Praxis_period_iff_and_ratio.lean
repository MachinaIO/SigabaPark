import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Common

/-- Canonical names make (a, b) -> name(a + b tau) periodic exactly on a + b tau = 0, and any nonzero period reveals tau. See note `pq-we-praxis-bilinear-substitutes`. -/
theorem AdvancedEncryption.WE.Praxis.period_iff_and_ratio {K X : Type*} [Field K] (ν : K → X) (hν : Function.Injective ν) (τ : K) :
    (∀ a b : K, (∀ x y : K, ν ((x + a) + (y + b) * τ) = ν (x + y * τ)) ↔ a + b * τ = 0) ∧
      ∀ a b : K, (a ≠ 0 ∨ b ≠ 0) → a + b * τ = 0 → b ≠ 0 ∧ τ = -a / b := by sorry

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Common
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

/-- Rank-one template: a nonzero symmetric rank-one matrix passes the Booleanity and constraint tests iff the system has a Boolean witness. See note `pq-we-praxis-bilinear-substitutes`. -/
theorem AdvancedEncryption.WE.Praxis.rankOne_passing_iff_witness {K : Type*} [Field K] {n : ℕ} {T : Type*}
    (a b c : T → Fin (n + 1) → K) :
    (∃ (κ : K) (v : Fin (n + 1) → K), κ ≠ 0 ∧ v ≠ 0 ∧
        (∀ j, κ * v j * v j = κ * v 0 * v j) ∧
        (∀ t, (∑ i, ∑ j, a t i * (κ * v i * v j) * b t j) = ∑ j, κ * v 0 * v j * c t j)) ↔
      ∃ w : Fin (n + 1) → K, w 0 = 1 ∧ (∀ j, w j = 0 ∨ w j = 1) ∧
        ∀ t, (∑ i, a t i * w i) * (∑ j, b t j * w j) = ∑ j, c t j * w j := by sorry

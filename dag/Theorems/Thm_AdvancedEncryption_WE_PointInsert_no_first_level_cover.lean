import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

open Matrix

/-- **Level-0 lock (note `pq-we-point-insertion-frontier`, §5).** Under the allowed-prefix invariant, if some prefix of length `ℓ ≥ 1` whose first bit is `b` is not allowed, then no pad and no clause can serve as a cover for a flip at level `0` towards bit `b`: such a cover (entry `1` at `(0, b)`, all-ones tail) would be alive on that prefix. -/
theorem AdvancedEncryption.WE.PointInsert.no_first_level_cover {ι κ : Type*} (clause : κ → ℕ → Bool → Bool)
    (pad : ι → ℕ → Bool → Bool) (T : ℕ → (ℕ → Bool) → Prop)
    (hT : ∀ k ℓ (x : ℕ → Bool), (∀ i, ℓ ≤ i → ∀ c, clause k i c = true) →
      (∀ i < ℓ, clause k i (x i) = true) → T ℓ x)
    (hJ : ∀ e ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, pad e i (x i) = true) → T ℓ x)
    (b : Bool) (x : ℕ → Bool) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hx0 : x 0 = b) (hx : ¬ T ℓ x)
    (cover : ℕ → Bool → Bool)
    (hcover : (∃ e, cover = pad e) ∨ ∃ k, cover = clause k)
    (h0 : cover 0 b = true) (htail : ∀ i, 0 < i → ∀ c, cover i c = true) : False := by sorry

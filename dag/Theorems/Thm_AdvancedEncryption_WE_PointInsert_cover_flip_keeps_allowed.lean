import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

open Matrix

/-- **Cover flips keep pads on allowed prefixes (note `pq-we-point-insertion-frontier`, §4).** A slot program `m : ℕ → Bool → Bool` gives the entry at level `i` for bit `c`; it is alive on the length-`ℓ` prefix of `x` when all entries along `x` below `ℓ` are `1`. A clause is fully falsified by that prefix when it is alive there and all its entries from level `ℓ` on are `1`. If every pad is alive only on allowed prefixes `T` and every fully falsifying prefix is allowed, then the cover flip of #111 (co-located cover, entry `1` at the flipped position, all-ones tail), with a pad or a clause as cover, keeps this property. -/
theorem AdvancedEncryption.WE.PointInsert.cover_flip_keeps_allowed {ι κ : Type*} (clause : κ → ℕ → Bool → Bool)
    (pad pad' : ι → ℕ → Bool → Bool) (T : ℕ → (ℕ → Bool) → Prop)
    (hT : ∀ k ℓ (x : ℕ → Bool), (∀ i, ℓ ≤ i → ∀ c, clause k i c = true) →
      (∀ i < ℓ, clause k i (x i) = true) → T ℓ x)
    (hJ : ∀ e ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, pad e i (x i) = true) → T ℓ x)
    (d : ι) (L : ℕ) (b : Bool) (cover : ℕ → Bool → Bool)
    (hcover : (∃ e, e ≠ d ∧ cover = pad e) ∨ ∃ k, cover = clause k)
    (hcol : ∀ i < L, ∀ c, pad d i c = cover i c)
    (hLb : cover L b = true)
    (htail : ∀ i, L < i → ∀ c, cover i c = true)
    (hother : ∀ e, e ≠ d → pad' e = pad e)
    (hd : ∀ i c, ¬ (i = L ∧ c = b) → pad' d i c = pad d i c) :
    ∀ e ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, pad' e i (x i) = true) → T ℓ x := by sorry

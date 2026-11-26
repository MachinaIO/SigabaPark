import Mathlib.Tactic.Common

/-- Depth-l class lock: walks of class-covered slot moves never create an all-ones slot (note `pq-we-class-lock`). -/
theorem AdvancedEncryption.WE.ClassLock.walk_lock {ι : Type*} (conf : ℕ → ι → ℕ → Bool → Bool) (ℓ : ℕ)
    (z : (ℕ → Bool → Bool) → ℕ → Bool)
    (hz : ∀ m m' : ℕ → Bool → Bool, (∀ i < ℓ, ∀ c, m i c = m' i c) → z m = z m')
    (hzcube : ∀ m : ℕ → Bool → Bool, (∀ i < ℓ, ∃ β, m i β = true) →
      ∀ i < ℓ, m i (z m i) = true)
    (h0 : ∀ e, ¬ ∀ i, conf 0 e i (z (conf 0 e) i) = true)
    (hstep : ∀ t, ∃ d, (∀ e, e ≠ d → conf (t + 1) e = conf t e) ∧
      ((∀ x : ℕ → Bool, (∀ i, conf (t + 1) d i (x i) = true) →
        ∃ e, (∀ i < ℓ, ∀ c, conf t e i c = conf (t + 1) d i c) ∧ ∀ i, conf t e i (x i) = true) ∨
       ∃ c L b, L < ℓ ∧ (∀ i < L, ∃ β, conf t c i β = true) ∧ conf t c L b = true ∧
         ∀ i, L < i → ∀ β, conf t c i β = true)) :
    ∀ t e, ¬ ∀ i β, conf t e i β = true := by sorry

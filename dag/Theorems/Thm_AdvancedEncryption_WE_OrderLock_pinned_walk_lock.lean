import Mathlib.Tactic.Common

/-- Pinned class lock for any level order: with some levels pinned to fixed values, class-covered slot moves and cover flips below depth l never create an all-ones slot (note `pq-we-order-lock`). -/
theorem AdvancedEncryption.WE.OrderLock.pinned_walk_lock {ι : Type*} (conf : ℕ → ι → ℕ → Bool → Bool) (ℓ : ℕ)
    (pin v : ℕ → Bool) (z : (ℕ → Bool → Bool) → ℕ → Bool)
    (hz : ∀ m m' : ℕ → Bool → Bool,
      (∀ i < ℓ, pin i = false → ∀ β, m i β = m' i β) → z m = z m')
    (hzpin : ∀ m i, pin i = true → z m i = v i)
    (hzcube : ∀ m : ℕ → Bool → Bool, (∀ i < ℓ, pin i = false → ∃ β, m i β = true) →
      ∀ i < ℓ, pin i = false → m i (z m i) = true)
    (h0 : ∀ e, ¬ ∀ i, conf 0 e i (z (conf 0 e) i) = true)
    (hstep : ∀ t, ∃ d, (∀ e, e ≠ d → conf (t + 1) e = conf t e) ∧
      ((∀ x : ℕ → Bool, (∀ i, conf (t + 1) d i (x i) = true) →
        ∃ e, (∀ i < ℓ, pin i = false → ∀ β, conf t e i β = conf (t + 1) d i β) ∧
          ∀ i, conf t e i (x i) = true) ∨
       ∃ c L b, L < ℓ ∧ (∀ i < L, ∀ β, conf t c i β = conf t d i β) ∧ conf t c L b = true ∧
         (∀ i, L < i → ∀ β, conf t c i β = true) ∧
         ∀ i β, ¬ (i = L ∧ β = b) → conf (t + 1) d i β = conf t d i β)) :
    ∀ t e, ¬ ∀ i β, conf t e i β = true := by sorry

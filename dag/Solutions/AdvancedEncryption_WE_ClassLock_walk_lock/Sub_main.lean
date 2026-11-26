import Mathlib.Tactic.Common

theorem solution {ι : Type*} (conf : ℕ → ι → ℕ → Bool → Bool) (ℓ : ℕ)
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
    ∀ t e, ¬ ∀ i β, conf t e i β = true := by
  have key : ∀ t e, ¬ ∀ i, conf t e i (z (conf t e) i) = true := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      obtain ⟨d, hother, hcov | ⟨c, L, b, hL, habove, hLb, htail⟩⟩ := hstep t
      · intro e he
        by_cases hed : e = d
        · subst hed
          obtain ⟨f, hfc, hfa⟩ := hcov _ he
          have hzf : z (conf t f) = z (conf (t + 1) e) := hz _ _ hfc
          exact ih f (by rw [hzf]; exact hfa)
        · rw [hother e hed] at he
          exact ih e he
      · exfalso
        have hne : ∀ i < ℓ, ∃ β, conf t c i β = true := by
          intro i hi
          rcases Nat.lt_trichotomy i L with h | h | h
          · exact habove i h
          · subst h; exact ⟨b, hLb⟩
          · exact ⟨true, htail i h true⟩
        apply ih c
        intro i
        by_cases hi : i < ℓ
        · exact hzcube _ hne i hi
        · exact htail i (by omega) _
  intro t e hfull
  exact key t e (fun i => hfull i _)

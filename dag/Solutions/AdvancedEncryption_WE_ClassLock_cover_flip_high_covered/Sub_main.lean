import Mathlib.Tactic.Common

theorem solution {ι : Type*} (pad : ι → ℕ → Bool → Bool) (ℓ : ℕ)
    (d c : ι) (L : ℕ) (b : Bool) (hℓL : ℓ ≤ L)
    (hcol : ∀ i < L, ∀ β, pad d i β = pad c i β) (hLb : pad c L b = true)
    (htail : ∀ i, L < i → ∀ β, pad c i β = true)
    (m' : ℕ → Bool → Bool) (hm' : ∀ i β, ¬ (i = L ∧ β = b) → m' i β = pad d i β) :
    ∀ x : ℕ → Bool, (∀ i, m' i (x i) = true) →
      ∃ e, (∀ i < ℓ, ∀ β, pad e i β = m' i β) ∧ ∀ i, pad e i (x i) = true := by
  intro x hx
  by_cases hxL : x L = b
  · refine ⟨c, ?_, ?_⟩
    · intro i hi β
      rw [hm' i β (fun h => by omega), hcol i (by omega)]
    · intro i
      rcases Nat.lt_trichotomy i L with h | h | h
      · rw [← hcol i h, ← hm' i (x i) (fun h' => by omega)]; exact hx i
      · subst h; rw [hxL]; exact hLb
      · exact htail i h _
  · refine ⟨d, ?_, ?_⟩
    · intro i hi β
      rw [hm' i β (fun h => by omega)]
    · intro i
      have : ¬ (i = L ∧ x i = b) := by
        rintro ⟨rfl, h⟩; exact hxL h
      rw [← hm' i (x i) this]; exact hx i

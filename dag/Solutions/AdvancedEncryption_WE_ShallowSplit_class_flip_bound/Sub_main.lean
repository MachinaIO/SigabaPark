import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Common

theorem solution {V U : Type*}
    (ℓ : ℕ → V → U → Bool) (n f : ℕ) (F : ℕ → U → Finset V)
    (hF : ∀ t x u, ℓ (t + 1) x u ≠ ℓ t x u → x ∈ F t u) (hf : ∀ t u, (F t u).card ≤ f)
    (h0 : ∀ x u, ℓ 0 x u = false) (hn : ∀ x u, ℓ n x u = true)
    (c : Finset V) (hc : ∀ t x y, x ∈ c → y ∈ c → ℓ t x = ℓ t y) (u : U) :
    c.card ≤ f := by
  classical
  rcases c.eq_empty_or_nonempty with hce | ⟨x₀, hx₀⟩
  · simp [hce]
  have hex : ∃ t, ℓ t x₀ u = true := ⟨n, hn x₀ u⟩
  have ht₁true : ℓ (Nat.find hex) x₀ u = true := Nat.find_spec hex
  have ht₁pos : Nat.find hex ≠ 0 := by
    intro h; rw [h, h0] at ht₁true; exact Bool.false_ne_true ht₁true
  obtain ⟨t, ht⟩ : ∃ t, Nat.find hex = t + 1 := Nat.exists_eq_succ_of_ne_zero ht₁pos
  have htfalse : ℓ t x₀ u = false := by
    have := Nat.find_min hex (show t < Nat.find hex by omega)
    simpa using this
  rw [ht] at ht₁true
  have hsub : c ⊆ F t u := by
    intro y hy
    apply hF
    rw [hc (t + 1) y x₀ hy hx₀, hc t y x₀ hy hx₀, ht₁true, htfalse]
    decide
  exact (Finset.card_le_card hsub).trans (hf t u)

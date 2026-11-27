import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Group

theorem AdvancedEncryption.WE.FusedRank.one_key_frame_fibers {G A B : Type} [Group G] (j₀ j₁ t : G)
    (l₀ l₁ : G → A) (r₀ r₁ : G → B)
    (hl : ∀ p, l₁ (t⁻¹ * p) = l₀ p)
    (hr : ∀ q, r₁ (q * (j₀⁻¹ * t * j₁)) = r₀ q) (v : A × G × B) :
    Nonempty ({p : G × G // (l₀ p.1, p.1⁻¹ * j₀ * p.2⁻¹, r₀ p.2) = v} ≃
      {p : G × G // (l₁ p.1, p.1⁻¹ * j₁ * p.2⁻¹, r₁ p.2) = v}) := by
  sorry

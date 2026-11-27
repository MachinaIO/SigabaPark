import Mathlib

theorem AdvancedEncryption.WE.TraceProject.chart_projection {P Q C Y : Type} (p : P) (chart : P → Q ≃ Q)
    (F : P → Q → Y) (emit : P → Q → C) (decode : P → C → Q)
    (exactProfile : ∀ q, F p (decode p (emit p q)) = F p q) (ψ : P → Y → Prop) :
    (∃ old, ψ p (F p (chart p old))) ↔ ∃ c, ψ p (F p (decode p c)) := by
  sorry

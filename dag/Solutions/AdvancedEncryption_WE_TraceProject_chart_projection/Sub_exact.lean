import Mathlib

theorem solution {P Q C Y : Type} (p : P) (chart : P → Q ≃ Q)
    (F : P → Q → Y) (emit : P → Q → C) (decode : P → C → Q)
    (exactProfile : ∀ q, F p (decode p (emit p q)) = F p q) (ψ : P → Y → Prop) :
    (∃ old, ψ p (F p (chart p old))) ↔ ∃ c, ψ p (F p (decode p c)) := by
  constructor
  · rintro ⟨old,h⟩
    exact ⟨emit p (chart p old), by rwa [exactProfile]⟩
  · rintro ⟨c,h⟩
    exact ⟨(chart p).symm (decode p c), by simpa using h⟩

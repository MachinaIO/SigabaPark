import Mathlib

theorem AdvancedEncryption.WE.NoisyFiber.OppositeCollision {S P T : Type*} [AddCommGroup S] [AddCommGroup P] [AddCommGroup T]
    (A : S →+ P) (c : S →+ T) (E : Set P) (half : T) :
    (∃ s t : S, ∃ e ∈ E, ∃ f ∈ E, A s + e = A t + f ∧ c s = c t + half) ↔
    (∃ d : S, ∃ e ∈ E, ∃ f ∈ E, A d = f-e ∧ c d = half) := by sorry

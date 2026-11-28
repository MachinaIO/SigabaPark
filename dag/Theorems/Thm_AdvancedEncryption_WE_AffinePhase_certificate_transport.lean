import Mathlib

theorem AdvancedEncryption.WE.AffinePhase.certificate_transport {K U V H : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [Fintype U] (L : U →ₗ[K] V)
    (cert : U) (target : V) (valid : L cert = target) (phase : H → K)
    (test : H → V → ℤ) (h : H) :
    (∑ u : U, test h (L u + phase h • target)) = ∑ u : U, test h (L u) := by sorry

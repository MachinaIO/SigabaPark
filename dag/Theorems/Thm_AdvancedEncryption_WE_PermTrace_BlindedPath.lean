import Mathlib

theorem AdvancedEncryption.WE.PermTrace.BlindedPath {G : Type*} [Group G] (frame raw plain blind : Nat → G)
    (hp : plain 0 = 1) (hb : blind 0 = 1)
    (ps : ∀ i, plain (i+1) = plain i * raw i)
    (bs : ∀ i, blind (i+1) = blind i * (frame i)⁻¹ * raw i * frame (i+1))
    (n : Nat) : blind n = (frame 0)⁻¹ * plain n * frame n := by sorry

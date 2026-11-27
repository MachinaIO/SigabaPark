import Mathlib

theorem AdvancedEncryption.WE.BranchTags.masked_view_count
    {X R G : Type*} [Finite X] [AddCommGroup R] [Finite R] [AddCommGroup G]
    (f : X → G) (mask : R →+ G) (y : G) :
    Nat.card {p : X × R // f p.1 + mask p.2 = y} =
      Nat.card {x : X // ∃ r, f x + mask r = y} * Nat.card mask.ker := by sorry

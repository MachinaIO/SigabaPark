import Definitions.Def_BucketLabel
open BucketLabel
theorem AdvancedEncryption.WE.BucketLabel.authorized {R I V : Type} [CommRing R] [AddCommGroup V] [Module R V] [Fintype I]
    (row : I → V →ₗ[R] R) (target c : I → R) (r : V) (b : R)
    (hcancel : ∑ i, c i * row i r = 0) (hvalue : ∑ i, c i * target i = 1) :
    (∑ i, c i * (row i r + target i * b)) = b := by sorry

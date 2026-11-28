import Definitions.Def_BucketLabel
open BucketLabel
theorem solution {R I T V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (key : I → T) (row : I → V →ₗ[R] R) (target : I → R) (h : T → V)
    (hr : ∀ i, row i (h (key i)) = target i)
    (r : T → V) (b : R) :
    release key row target (fun t => r t + b • h t) 0 = release key row target r b := by
  funext i
  simp [release, hr, mul_comm]

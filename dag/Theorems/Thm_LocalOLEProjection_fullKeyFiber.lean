import Definitions.Def_LocalOLEProjection
import Mathlib.SetTheory.Cardinal.Finite

theorem LocalOLEProjection.fullKeyFiber {R : Type*} [CommRing R] (I J : Ideal R)
    (h : IsCoprime I J) (b : R) (v : (R ⧸ I) × (R ⧸ J)) :
    Nat.card {r : R ⧸ (I * J) // LocalOLEProjection.issue I J b r = v} = 1 := by sorry

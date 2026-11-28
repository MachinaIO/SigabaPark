import Definitions.Def_LocalOLEProjection
import Mathlib.SetTheory.Cardinal.Finite

theorem solution {R : Type*} [CommRing R] (I J : Ideal R)
    (h : IsCoprime I J) (b : R) (v : (R ⧸ I) × (R ⧸ J)) :
    Nat.card {r : R ⧸ (I * J) // LocalOLEProjection.issue I J b r = v} = 1 := by
  obtain ⟨r, hr, hu⟩ := LocalOLEProjection.uniqueNonce I J h b v
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨r, hr⟩, ?_⟩
  intro y
  exact Subtype.ext (hu y.val y.property)

import Definitions.Def_PacketTraceBasis
import Mathlib.Tactic

theorem PacketTraceBasis.sameSpan {R M I J : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (actual : I → M) (virtual : J → M) (f g : M →ₗ[R] R)
    (same : Submodule.span R (Set.range actual) = Submodule.span R (Set.range virtual)) :
    PacketTraceBasis.rowsAgree actual f g ↔ PacketTraceBasis.rowsAgree virtual f g := by
  sorry

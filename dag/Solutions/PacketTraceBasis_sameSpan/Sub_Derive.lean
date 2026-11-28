import Definitions.Def_PacketTraceBasis
import Mathlib.Tactic

private theorem criterion {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (f g : M →ₗ[R] R) {K : Type*} (rows : K → M) :
      PacketTraceBasis.rowsAgree rows f g ↔
        Submodule.span R (Set.range rows) ≤ LinearMap.ker (f - g) := by
  rw [Submodule.span_le]
  constructor
  · intro h v hv
    obtain ⟨i, rfl⟩ := hv
    change f (rows i) - g (rows i) = 0
    exact sub_eq_zero.mpr (h i)
  · intro h i
    have hz := h (Set.mem_range_self i)
    change f (rows i) - g (rows i) = 0 at hz
    exact sub_eq_zero.mp hz

theorem solution {R M I J : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (actual : I → M) (virtual : J → M) (f g : M →ₗ[R] R)
    (same : Submodule.span R (Set.range actual) = Submodule.span R (Set.range virtual)) :
    PacketTraceBasis.rowsAgree actual f g ↔ PacketTraceBasis.rowsAgree virtual f g := by
  rw [criterion f g actual, criterion f g virtual, same]

import Mathlib

theorem solution {K X Y Z : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
    (L : X →ₗ[K] Y) (D : Y →ₗ[K] X) (E : Z →ₗ[K] Y) (H : Y →ₗ[K] Z)
    (annihilates : H.comp L = 0) (decomposition : L.comp D + E.comp H = LinearMap.id)
    (y : Y) : (H y = 0 ↔ ∃ x, L x = y) ∧ (H y = 0 → L (D y) = y) := by
  have sectionAt (hy : H y = 0) : L (D y) = y := by
    have h := LinearMap.congr_fun decomposition y
    simpa [LinearMap.comp_apply, hy] using h
  refine ⟨⟨fun hy ↦ ⟨D y, sectionAt hy⟩, ?_⟩, sectionAt⟩
  rintro ⟨x, rfl⟩
  exact LinearMap.congr_fun annihilates x

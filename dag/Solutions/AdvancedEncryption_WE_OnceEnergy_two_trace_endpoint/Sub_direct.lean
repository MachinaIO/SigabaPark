import Mathlib
/-- Two different public energies interpolate to the hidden affine zero-energy endpoint. -/
theorem solution {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (L : V →ₗ[K] K) (d ρ q₀ q₁ : K) (s₀ s₁ : V)
    (h₀ : L s₀+d=ρ*q₀) (h₁ : L s₁+d=ρ*q₁) (h : q₀ ≠ q₁) :
    let t := q₀/(q₀-q₁)
    L ((1-t) • s₀ + t • s₁)+d = 0 := by
  dsimp
  rw [map_add,map_smul,map_smul]
  simp only [smul_eq_mul]
  have he : q₀-q₁ ≠ 0 := sub_ne_zero.mpr h
  field_simp
  linear_combination q₀*h₁ - q₁*h₀

import Mathlib
/-- Publicly gauge-masked zero and one edges expose same-frame generator directions and commutators. -/
theorem solution {G : Type*} [Group G] (r₀ r s u v : G) :
    let p := r₀⁻¹*r
    let left := r⁻¹*u*s
    let zero := r⁻¹*s
    let dir := p*left*zero⁻¹*p⁻¹
    dir = r₀⁻¹*u*r₀ ∧
      dir*(r₀⁻¹*v*r₀)*dir⁻¹*(r₀⁻¹*v*r₀)⁻¹ = r₀⁻¹*(u*v*u⁻¹*v⁻¹)*r₀ := by
  dsimp
  constructor <;> group

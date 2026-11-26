import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.LinearCombination

open LinearMap

theorem solution {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] {k : ℕ}
    (L R P : Fin k → V →ₗ[K] K) (out : V →ₗ[K] K) (l r : Fin k → K) (u : K)
    (measure : V → W) (decode : W → Fin k → K)
    (hread : ∀ v i, decode (measure v) i = L i v + l i) :
    let sys := fun z : Fin k → K ↦ (LinearMap.pi L).prod
      ((LinearMap.pi fun i ↦ P i + z i • R i).prod out)
    let rhs := fun z : Fin k → K ↦
      ((fun i ↦ z i - l i), (fun i ↦ 1 - z i * r i), 1 - u)
    (∀ v : V, ((∀ i, P i v = 1 - (L i v + l i) * (R i v + r i)) ∧ out v + u = 1) ↔
      sys (decode (measure v)) v = rhs (decode (measure v))) ∧
    ((∃ v : V, (∀ i, P i v = 1 - (L i v + l i) * (R i v + r i)) ∧ out v + u = 1) ↔
      ∃ t : W, rhs (decode t) ∈ LinearMap.range (sys (decode t))) := by
  dsimp only
  have fixed (z : Fin k → K) (v : V) :
      ((LinearMap.pi L).prod ((LinearMap.pi fun i ↦ P i + z i • R i).prod out)) v =
        ((fun i ↦ z i - l i), (fun i ↦ 1 - z i * r i), 1 - u) ↔
      (∀ i, L i v + l i = z i) ∧
      (∀ i, P i v = 1 - (L i v + l i) * (R i v + r i)) ∧ out v + u = 1 := by
    change ((fun i ↦ L i v), (fun i ↦ P i v + z i * R i v), out v) = _ ↔ _
    simp only [Prod.mk.injEq, funext_iff]
    constructor
    · rintro ⟨hl, hr, ho⟩
      have h i : L i v + l i = z i := by rw [hl i]; ring
      exact ⟨h, fun i ↦ by rw [h i]; linear_combination hr i, by linear_combination ho⟩
    · rintro ⟨hl, hr, ho⟩
      refine ⟨fun i ↦ by rw [← hl i]; ring, fun i ↦ ?_, by linear_combination ho⟩
      rw [← hl i, hr i]
      ring
  constructor
  · intro v
    rw [fixed]
    simp [hread]
  · constructor
    · rintro ⟨v, hv⟩
      exact ⟨measure v, v, (fixed _ v).2 ⟨fun i ↦ (hread v i).symm, hv⟩⟩
    · rintro ⟨z, v, hv⟩
      exact ⟨v, ((fixed (decode z) v).1 hv).2⟩

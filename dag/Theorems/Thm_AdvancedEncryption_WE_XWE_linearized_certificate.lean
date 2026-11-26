import SigabaNeoStd

open LinearMap

theorem AdvancedEncryption.WE.XWE.linearized_certificate {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] {k : ℕ}
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
  sorry

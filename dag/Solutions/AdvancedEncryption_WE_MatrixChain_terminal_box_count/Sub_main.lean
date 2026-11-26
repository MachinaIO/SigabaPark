import Mathlib

theorem solution {R U : Type*} [Ring R] [Fintype R] [Fintype U]
    (t : ℕ) (a : Rˣ) (rest : U → Fin t → R) (s : Finset R) [DecidableEq R] :
    Fintype.card {v : (Fin t → R) × U // ∀ i, (a : R) * v.1 i + rest v.2 i ∈ s} =
      s.card ^ t * Fintype.card U := by
  classical
  let e : {v : (Fin t → R) × U // ∀ i, (a : R) * v.1 i + rest v.2 i ∈ s} ≃
      (Fin t → ↥s) × U :=
    { toFun := fun v => (fun i => ⟨_, v.property i⟩, v.val.2)
      invFun := fun z => ⟨(fun i => (↑(a⁻¹) : R) * ((z.1 i : R) - rest z.2 i), z.2), by
        intro i
        simp [← mul_assoc]⟩
      left_inv := by
        intro v
        apply Subtype.ext
        apply Prod.ext
        · funext i
          simp [← mul_assoc]
        · rfl
      right_inv := by
        intro z
        apply Prod.ext
        · funext i
          apply Subtype.ext
          simp [← mul_assoc]
        · rfl }
  simpa using Fintype.card_congr e

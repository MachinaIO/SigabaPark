import Definitions.Def_NandWalshBox
open NandWalshBox
theorem solution :
    ({M : Matrix (Fin 4) (Fin 4) ℚ | admissible M} : Set _) =
      (doublyStochastic ℚ (Fin 4) : Set _) ∧
    Set.extremePoints ℚ {M : Matrix (Fin 4) (Fin 4) ℚ | admissible M} =
      {σ.permMatrix ℚ | σ : Equiv.Perm (Fin 4)} ∧
    (∀ u v : Fin 4, forbidden (raw u v) = true ↔
      (u = 0 ∧ v ≠ 0) ∨ (u ≠ 0 ∧ v = 0)) := by
  have eqs : ({M : Matrix (Fin 4) (Fin 4) ℚ | admissible M} : Set _) =
      (doublyStochastic ℚ (Fin 4) : Set _) := by
    ext M
    change admissible M ↔ M ∈ doublyStochastic ℚ (Fin 4)
    rw [mem_doublyStochastic_iff_sum]
    constructor
    · rintro ⟨non,tot,ru,cv⟩
      refine ⟨non,rowOnes _ tot ru, rowOnes _ ?_ cv⟩
      rw [Finset.sum_comm]
      exact tot
    · rintro ⟨non,r,c⟩
      exact ⟨non, by simp [r], by simp [zeroThree,r], by simp [zeroThree,c]⟩
  refine ⟨eqs, ?_, ?_⟩
  · rw [eqs, extremePoints_doublyStochastic]
  · decide

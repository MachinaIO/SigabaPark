import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

open Matrix Module

theorem solution {K : Type*} [Field K] {S U κ : Type*} [Fintype U] [Fintype κ] {m : ℕ}
    (X : Matrix S κ K) (E : Matrix S (Fin m) K) (ΔY : Matrix (κ ⊕ Fin m) U K) :
    (fromCols X E * ΔY).rank ≤ (fromCols X E).rank ∧ (fromCols X E).rank ≤ X.rank + m := by
  refine ⟨rank_mul_le_left _ _, ?_⟩
  have hr : LinearMap.range (fromCols X E).mulVecLin =
      LinearMap.range X.mulVecLin ⊔ LinearMap.range E.mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      simp only [mulVecLin_apply, fromCols_mulVec]
      exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
    · refine sup_le ?_ ?_
      · rintro _ ⟨v, rfl⟩
        exact ⟨Sum.elim v 0, by simp⟩
      · rintro _ ⟨v, rfl⟩
        exact ⟨Sum.elim 0 v, by simp⟩
  unfold Matrix.rank
  rw [hr]
  have := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range X.mulVecLin)
    (LinearMap.range E.mulVecLin)
  have hE := E.rank_le_card_width
  simp only [Fintype.card_fin] at hE
  unfold Matrix.rank at hE
  omega

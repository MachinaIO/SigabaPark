import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

open Matrix Module

theorem solution {K : Type*} [Field K] {S U κ : Type*} [Fintype S] [Fintype U] [Fintype κ]
    {m : ℕ} (X : Matrix S κ K) (E : Matrix S (Fin m) K) (ΔY : Matrix (κ ⊕ Fin m) U K)
    (hY : ΔY.rank = Fintype.card κ + m) :
    (fromCols X E * ΔY).rank = X.rank + m ↔
      E.rank = m ∧ Disjoint (LinearMap.range X.mulVecLin) (LinearMap.range E.mulVecLin) := by
  have htop : LinearMap.range ΔY.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hY, finrank_pi, Fintype.card_sum, Fintype.card_fin]
  have hV : (fromCols X E * ΔY).rank = (fromCols X E).rank := by
    unfold Matrix.rank
    rw [mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ htop]
  rw [hV]
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
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range X.mulVecLin)
    (LinearMap.range E.mulVecLin)
  have hE := E.rank_le_card_width
  simp only [Fintype.card_fin] at hE
  unfold Matrix.rank at hE
  rw [disjoint_iff, ← Submodule.finrank_eq_zero]
  omega

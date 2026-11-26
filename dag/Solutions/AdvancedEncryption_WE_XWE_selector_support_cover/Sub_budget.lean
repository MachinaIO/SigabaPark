import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Choose

theorem solution (K : Type*) [Field K] {m n : ℕ} (S : Fin m → Finset (Fin n)) (d : ℕ) :
    (∃ A : Matrix (Fin m) (Fin n) K, A.rank ≤ d ∧
      (∀ i, ∃ j, A i j ≠ 0) ∧ ∀ i j, A i j ≠ 0 → j ∈ S i) ↔
    ∃ C : Finset (Fin n), C.card ≤ d ∧ ∀ i, ∃ j ∈ C, j ∈ S i := by
  classical
  constructor
  · rintro ⟨A, hr, hrow, hs⟩
    obtain ⟨f, hf, hspan, _⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.col)
    choose col hc using hf
    refine ⟨Finset.univ.image col, ?_, ?_⟩
    · apply Finset.card_image_le.trans
      simpa [A.rank_eq_finrank_span_cols] using hr
    · intro i
      obtain ⟨j, hj⟩ := hrow i
      have hn : ∃ a, f a i ≠ 0 := by
        by_contra! h
        let ev : (Fin m → K) →ₗ[K] K := LinearMap.proj i
        have hk : Submodule.span K (Set.range f) ≤ LinearMap.ker ev := by
          apply Submodule.span_le.mpr
          rintro _ ⟨a, rfl⟩
          exact h a
        rw [hspan] at hk
        exact hj (hk (Submodule.subset_span (Set.mem_range_self j)))
      obtain ⟨a, ha⟩ := hn
      refine ⟨col a, Finset.mem_image_of_mem col (Finset.mem_univ _), hs _ _ ?_⟩
      simpa only [← Matrix.col_apply, hc] using ha
  · rintro ⟨C, hd, hcover⟩
    choose j hj hs using hcover
    let row := fun v : Fin n ↦ (Pi.single v (1 : K) : Fin n → K)
    let A : Matrix (Fin m) (Fin n) K := fun i ↦ row (j i)
    refine ⟨A, ?_, fun i ↦ ⟨j i, by simp [A, row]⟩, ?_⟩
    · rw [A.rank_eq_finrank_span_row]
      have hsub : Set.range A.row ⊆ Set.range (fun c : C ↦ row c.val) := by
        rintro _ ⟨i, rfl⟩
        exact ⟨⟨j i, hj i⟩, rfl⟩
      apply (Submodule.finrank_mono (Submodule.span_mono hsub)).trans
      exact (finrank_range_le_card (R := K) _).trans (by simpa using hd)
    · intro i v hv
      by_cases he : v = j i
      · simpa [he] using hs i
      · exact False.elim (hv (Pi.single_eq_of_ne he _))

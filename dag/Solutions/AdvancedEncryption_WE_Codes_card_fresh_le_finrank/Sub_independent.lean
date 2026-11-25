import Mathlib

theorem solution {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {M : ℕ} (v : Fin M → V) :
    {r | v r ∉ Submodule.span K (v '' {t | r < t})}.ncard ≤ Module.finrank K V := by
  classical
  set S := {r | v r ∉ Submodule.span K (v '' {t | r < t})} with hS
  have hli : LinearIndependent K (fun r : S => v r) := by
    rw [linearIndependent_iff']
    intro s g hsum
    by_contra hne
    push Not at hne
    obtain ⟨i, hi, hgi⟩ := hne
    set s' := s.filter (fun j => g j ≠ 0) with hs'
    have hne' : s'.Nonempty := ⟨i, by simp [hs', hi, hgi]⟩
    set i0 := s'.min' hne' with hi0
    have hi0mem : i0 ∈ s' := Finset.min'_mem _ _
    have hgi0 : g i0 ≠ 0 := (Finset.mem_filter.mp hi0mem).2
    have hi0s : i0 ∈ s := (Finset.mem_filter.mp hi0mem).1
    -- split the sum at i0
    have hsplit : g i0 • v i0 = - ∑ j ∈ s.erase i0, g j • v j := by
      rw [← Finset.add_sum_erase s _ hi0s] at hsum
      exact eq_neg_of_add_eq_zero_left hsum
    have hmem : ∑ j ∈ s.erase i0, g j • v j ∈ Submodule.span K (v '' {t | (i0 : Fin M) < t}) := by
      apply Submodule.sum_mem
      intro j hj
      by_cases hgj : g j = 0
      · simp [hgj]
      · apply Submodule.smul_mem
        apply Submodule.subset_span
        refine ⟨j, ?_, rfl⟩
        have hjs : j ∈ s := Finset.mem_of_mem_erase hj
        have hjne : j ≠ i0 := Finset.ne_of_mem_erase hj
        have hjs' : j ∈ s' := by simp [hs', hjs, hgj]
        have hle : i0 ≤ j := Finset.min'_le _ _ hjs'
        have hlt : i0 < j := lt_of_le_of_ne hle (Ne.symm hjne)
        exact hlt
    have hv : v i0 ∈ Submodule.span K (v '' {t | (i0 : Fin M) < t}) := by
      have : v i0 = (g i0)⁻¹ • (g i0 • v i0) := by
        rw [smul_smul, inv_mul_cancel₀ hgi0, one_smul]
      rw [this, hsplit]
      exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hmem)
    exact (i0 : S).2 hv
  have := hli.fintype_card_le_finrank
  rw [Set.ncard_eq_toFinset_card']
  simpa [Set.toFinset_card] using this

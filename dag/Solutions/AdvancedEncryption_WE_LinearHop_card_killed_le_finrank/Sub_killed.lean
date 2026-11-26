import Mathlib

theorem solution {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {M : ℕ}
    (h : Fin M → Module.Dual K V) (L : Fin M → (U →ₗ[K] V)) :
    {r | (∀ t, r < t → (h t).comp (L r) = 0) ∧ (h r).comp (L r) ≠ 0}.ncard
      ≤ Module.finrank K V := by
  classical
  set S := {r | h r ∉ Submodule.span K (h '' {t | r < t})} with hS
  have hsub : {r | (∀ t, r < t → (h t).comp (L r) = 0) ∧ (h r).comp (L r) ≠ 0} ⊆ S := by
    intro r ⟨hlive, hkill⟩ hmem
    -- the map g ↦ g ∘ L r is linear and kills the span of the later functionals
    let T : Module.Dual K V →ₗ[K] (U →ₗ[K] K) := LinearMap.lcomp K K (L r)
    have hspan : Submodule.span K (h '' {t | r < t}) ≤ LinearMap.ker T := by
      rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      exact hlive t ht
    exact hkill (hspan hmem)
  have hli : LinearIndependent K (fun r : S => h r) := by
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
    have hsplit : g i0 • h i0 = - ∑ j ∈ s.erase i0, g j • h j := by
      rw [← Finset.add_sum_erase s _ hi0s] at hsum
      exact eq_neg_of_add_eq_zero_left hsum
    have hmem : ∑ j ∈ s.erase i0, g j • h j ∈ Submodule.span K (h '' {t | (i0 : Fin M) < t}) := by
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
        exact lt_of_le_of_ne hle (Ne.symm hjne)
    have hv : h i0 ∈ Submodule.span K (h '' {t | (i0 : Fin M) < t}) := by
      have : h i0 = (g i0)⁻¹ • (g i0 • h i0) := by
        rw [smul_smul, inv_mul_cancel₀ hgi0, one_smul]
      rw [this, hsplit]
      exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hmem)
    exact (i0 : S).2 hv
  have hcard := hli.fintype_card_le_finrank
  have hS' : S.ncard ≤ Module.finrank K V := by
    rw [Set.ncard_eq_toFinset_card', Subspace.dual_finrank_eq.symm]
    simpa [Set.toFinset_card] using hcard
  exact (Set.ncard_le_ncard hsub).trans hS'

import Mathlib

theorem solution {K X E P : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup E] [Module K E] [AddCommGroup P] [Module K P]
    (equations : X →ₗ[K] E) (ports : X →ₗ[K] P) (rhs : E) (guard : P → Prop)
    {ι : Type*} (check : ι → Module.Dual K (E × P))
    (complete : Submodule.span K (Set.range check) =
      (LinearMap.range (equations.prod ports)).dualAnnihilator) (y : P) :
    (∃ x, equations x = rhs ∧ ports x = y ∧ guard (ports x)) ↔
      guard y ∧ ∀ i, check i (rhs, y) = 0 := by
  let L := equations.prod ports
  have dual := Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
    (LinearMap.range L) (rhs, y)
  constructor
  · rintro ⟨x, hx, hy, hg⟩
    refine ⟨hy ▸ hg, fun i ↦ dual.mpr ⟨x, Prod.ext hx hy⟩ _ ?_⟩
    rw [← complete]
    exact Submodule.subset_span ⟨i, rfl⟩
  · rintro ⟨hg, h⟩
    have le : Submodule.span K (Set.range check) ≤
        LinearMap.ker (Module.Dual.eval K (E × P) (rhs,y)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact h i
    obtain ⟨x,hx⟩ := dual.mp (fun f hf ↦ le (complete.symm ▸ hf))
    have hy : ports x = y := congrArg Prod.snd hx
    exact ⟨x, congrArg Prod.fst hx, hy, hy.symm ▸ hg⟩

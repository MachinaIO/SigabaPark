import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic

theorem solution {K V U ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup U] [Module K U]
    (φ : ι → V →ₗ[K] U) (S : Finset ι)
    (hfresh : ∀ w ∈ S, ∃ x : V, φ w x ≠ 0 ∧ ∀ v ∈ S, v ≠ w → φ v x = 0) :
    S.card ≤ Module.finrank K V := by
  classical
  choose x hx using hfresh
  let y : S → V := fun w => x w.1 w.2
  have hli : LinearIndependent K y := by
    rw [Fintype.linearIndependent_iff]
    intro c hc w
    have := congrArg (φ w.1) hc
    rw [map_sum, map_zero, Finset.sum_eq_single w] at this
    · rw [map_smul] at this
      exact (smul_eq_zero.mp this).resolve_right (hx w.1 w.2).1
    · intro v _ hvw
      rw [map_smul, (hx v.1 v.2).2 w.1 w.2 (fun h => hvw (Subtype.ext h.symm)), smul_zero]
    · intro h; exact absurd (Finset.mem_univ w) h
  simpa using hli.fintype_card_le_finrank

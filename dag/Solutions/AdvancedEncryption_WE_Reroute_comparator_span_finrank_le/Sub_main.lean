import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Common

theorem solution {K V S R : Type*} [Field K] [Fintype S] [Fintype R] [DecidableEq S]
    (κ : V → S) (ρ : R → K) :
    Module.finrank K (Submodule.span K (Set.range fun x : V =>
      fun sr : S × R => if sr.1 = κ x then ρ sr.2 else 0)) ≤ Fintype.card S := by
  let g : S → S × R → K := fun s sr => if sr.1 = s then ρ sr.2 else 0
  have hsub : Set.range (fun x : V => fun sr : S × R => if sr.1 = κ x then ρ sr.2 else 0)
      ⊆ Set.range g := by
    rintro _ ⟨x, rfl⟩; exact ⟨κ x, rfl⟩
  exact (Submodule.finrank_mono (Submodule.span_mono hsub)).trans (finrank_range_le_card g)

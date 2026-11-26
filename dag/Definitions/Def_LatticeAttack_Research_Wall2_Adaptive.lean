module

public import Definitions.Def_LatticeAttack_Research_Wall2_Incidence

set_option autoImplicit true

public section

namespace SigabaNeo.Wall2

open Finset

/-- Count failures of any selector using fixed candidate events on the same input space. -/
theorem adaptiveFailures {Ω I : Type*} [Fintype I] [DecidableEq Ω]
    (inputs : Finset Ω) (bad : I → Finset Ω) (pick : Ω → I) :
    (inputs.filter fun x ↦ x ∈ bad (pick x)).card ≤ ∑ i, (bad i).card := by
  classical
  apply le_trans _ (card_biUnion_le (s := univ) (t := bad))
  apply card_le_card
  intro x hx
  exact mem_biUnion.mpr ⟨pick x, mem_univ _, (mem_filter.mp hx).2⟩

/-- Singleton failures of fixed descriptions can cover every selected input. -/
theorem diagonalSelection (N : ℕ) :
    (∀ i : Fin N, ({i} : Finset (Fin N)).card = 1) ∧
    (univ.filter fun x : Fin N ↦ x ∈ ({x} : Finset (Fin N))).card = N := by
  simp

#print axioms adaptiveFailures
#print axioms diagonalSelection

end SigabaNeo.Wall2

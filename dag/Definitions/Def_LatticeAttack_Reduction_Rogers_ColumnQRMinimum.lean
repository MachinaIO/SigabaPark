module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRPotential

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Rogers

/-- Minimize over the finite set of potential values below the initial candidate's value. -/
theorem ColumnCandidate.exists_minimum_of_finite_sublevel {n : ℕ} {x : SL n}
    (initial : ColumnCandidate x)
    (finite : {v : ℝ | ∃ c : ColumnCandidate x,
      c.potential = v ∧ v ≤ initial.potential}.Finite) :
    ∃ c : ColumnCandidate x, ∀ b : ColumnCandidate x, c.potential ≤ b.potential := by
  obtain ⟨v, ⟨c, rfl, hc⟩, hmin⟩ := Set.exists_min_image _ id finite
    ⟨initial.potential, initial, rfl, le_rfl⟩
  refine ⟨c, fun b ↦ ?_⟩
  by_cases hb : b.potential ≤ initial.potential
  · exact hmin _ ⟨b, rfl, hb⟩
  · exact hc.trans (le_of_not_ge hb)

end SigabaNeo.Rogers

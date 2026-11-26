module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_MeanValue

set_option autoImplicit true

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal Pointwise
namespace SigabaNeo.Rogers

/-- Inverse images give right translates for the right arithmetic quotient.
The height bound is written without a square root. -/
def siegelSetTwo : Set (SL 2) :=
  {g | let z := g⁻¹ • UpperHalfPlane.I
       |z.re| ≤ 1/2 ∧ 3 ≤ 4 * z.im ^ 2}

theorem siegelSetTwo_covers (x : SL 2) :
    ∃ g : (integerGroup 2).op, x ∈ g • siegelSetTwo := by
  let φ := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin 2)
  let z := x⁻¹ • UpperHalfPlane.I
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd z
  let g : (integerGroup 2).op := ⟨MulOpposite.op (φ γ), γ, rfl⟩
  refine ⟨g, x * (φ γ)⁻¹, ?_, ?_⟩
  · change |(_ • UpperHalfPlane.I : UpperHalfPlane).re| ≤ _ ∧ _
    rw [mul_inv_rev, inv_inv, mul_smul]
    change |(γ • z).re| ≤ _ ∧ 3 ≤ 4 * (γ • z).im ^ 2
    exact ⟨hγ.2, ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ⟩
  · change x * (φ γ)⁻¹ * φ γ = x
    simp

#print axioms siegelSetTwo_covers

end SigabaNeo.Rogers

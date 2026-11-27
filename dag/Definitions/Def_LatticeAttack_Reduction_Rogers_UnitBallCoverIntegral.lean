import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelDensityTests
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnGramParameters
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnBorelSubgroup

set_option autoImplicit true

open MeasureTheory Set
open scoped Pointwise ENNReal

namespace SigabaNeo.Rogers
local instance (n : ℕ) : Countable (Matrix (Fin n) (Fin n) ℤ) :=
  inferInstanceAs (Countable (Fin n → Fin n → ℤ))

local instance (n : ℕ) : BorelSpace (SL n) := ⟨rfl⟩

/-- Integrating a quotient workload over a covering set bounds its fundamental-domain integral. -/
theorem densityWork_domain_le_cover {n : ℕ} (j : ℕ) {D S : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (cover : ∀ x : SL n, ∃ γ : (integerGroup n).op, x ∈ γ • S) :
    ∫⁻ g in D, densityWork n j g ∂groupHaar n ≤ ∫⁻ g in S, densityWork n j g ∂groupHaar n := by
  let φ := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin n)
  have : Countable (Matrix.SpecialLinearGroup (Fin n) ℤ) := Subtype.val_injective.countable
  have : Countable (integerGroup n) := φ.rangeRestrict_surjective.countable
  have : Countable (integerGroup n).op := (integerGroup n).equivOp.surjective.countable
  let := groupHaar_rightInvariant n
  have inv (γ : (integerGroup n).op) (x : SL n) : densityWork n j (γ • x) = densityWork n j x := by
    unfold densityWork
    congr 1
    exact QuotientGroup.mk_mul_of_mem x γ.property
  rw [hd.setLIntegral_eq_tsum' (densityWork n j) S]
  simp only [inv]
  refine (lintegral_mono_set (t := ⋃ γ : (integerGroup n).op, γ • S ∩ D) ?_).trans
    (lintegral_iUnion_le _ _)
  intro x hx
  obtain ⟨γ, hγ⟩ := cover x
  exact mem_iUnion.mpr ⟨γ, hγ, hx⟩

/-- Reciprocal QR diagonal lengths bound the widths of the integer-coordinate fibers.
The inverse volume normalizes the unit-ball count in `densityWork`. -/
noncomputable def unitBallQRBound (d : ℕ) (g : SL (d+1)) : ℝ≥0∞ :=
  (volume (densityBall (d+1) 0))⁻¹ * ENNReal.ofReal
    (∏ i, (1 + 2 * Real.exp (-columnDiagLogs (gramColumnParameters g).1 i)))

end SigabaNeo.Rogers

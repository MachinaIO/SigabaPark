import Definitions.Def_LatticeAttack_Attacks_Bkw_Coded
import Definitions.Def_LatticeAttack_Attacks_Dual_Assembled

set_option autoImplicit true

/-!
# Coded BKW with a bounded, symmetric residual: explicit `c_code`

`coded_recovery` takes a lower bound `c_code` on the real character mean of the residual
`⟨t, δ⟩` as a hypothesis. Here it is discharged for any residual law supported on reductions
of integer vectors in `[−B, B]^b` and symmetric under `δ ↦ −δ` (pairing two draws from the same
coset class gives such a law), with the remaining-secret block `t` a reduction of an integer
vector of Euclidean norm `≤ T₀`:
`c_code = 1 − (2π T₀ B √b / q)² / 2` (from `DualMoments.bounded_dual_bias`).
-/

open MeasureTheory SigabaNeo.DualMoments
open scoped Matrix

namespace SigabaNeo.Lattices.Attacks.Bkw

variable {q b k N : ℕ} [NeZero q] [MeasurableSingletonClass (Residues q b)]

/-- Bounded residuals give an explicit lower bound on the residual's real character mean. -/
theorem box_residual_lower (ν : Measure (Residues q b)) [IsProbabilityMeasure ν]
    (t : Residues q b) (tl : Fin b → ℤ) (htl : t = fun j ↦ (tl j : ZMod q))
    {T₀ B : ℝ} (hT : Real.sqrt (∑ j, ((tl j : ℤ) : ℝ) ^ 2) ≤ T₀) (hB : 0 ≤ B)
    (hν : ∀ d, ν.real {d} ≠ 0 → ∃ dl : Fin b → ℤ, (∀ j, |((dl j : ℤ) : ℝ)| ≤ B) ∧
      d = fun j ↦ (dl j : ZMod q)) :
    1 - (2 * Real.pi / q * (T₀ * B * Real.sqrt b)) ^ 2 / 2 ≤
      (∫ d, ZMod.stdAddChar (t ⬝ᵥ d) ∂ν).re := by
  have h := bounded_dual_bias (W := Unit) (fun _ ↦ t) (fun _ ↦ tl) (fun _ ↦ htl)
    (fun _ ↦ hT) hB (Measure.dirac ()) ν hν
  rw [integral_dirac] at h
  refine h.trans_eq ?_
  have hre : (∫ d, ZMod.stdAddChar (t ⬝ᵥ d) ∂ν).re = ∫ d, (ZMod.stdAddChar (t ⬝ᵥ d) : ℂ).re ∂ν :=
    (integral_re (𝕜 := ℂ) (f := fun d ↦ (ZMod.stdAddChar (t ⬝ᵥ d) : ℂ)) Integrable.of_finite).symm
  rw [hre]
  rfl

/-- **Coded BKW recovery with a bounded symmetric residual.** -/
theorem coded_box_recovery (μ : Measure (ZMod q)) (ν : Measure (Residues q b))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : Residues q b) (tl : Fin b → ℤ) (htl : t = fun j ↦ (tl j : ZMod q))
    {T₀ B : ℝ} (hT : Real.sqrt (∑ j, ((tl j : ℤ) : ℝ) ^ 2) ≤ T₀) (hB : 0 ≤ B)
    (hν : ∀ d, ν.real {d} ≠ 0 → ∃ dl : Fin b → ℤ, (∀ j, |((dl j : ℤ) : ℝ)| ≤ B) ∧
      d = fun j ↦ (dl j : ZMod q))
    (hs : ∀ d : Residues q b, ν {d} = ν {-d})
    (s : Residues q k) (R : Measure (Residues q k)) [IsProbabilityMeasure R]
    (hR : ∀ r, R.real {r} = (Fintype.card (Residues q k) : ℝ)⁻¹)
    {c_err : ℝ} (ha : 0 < c_err)
    (he : (∫ z, ZMod.stdAddChar z ∂μ).im = 0)
    (hμ : c_err ≤ (∫ z, ZMod.stdAddChar z ∂μ).re)
    (hc : 0 < 1 - (2 * Real.pi / q * (T₀ * B * Real.sqrt b)) ^ 2 / 2) :
    let c := c_err * (1 - (2 * Real.pi / q * (T₀ * B * Real.sqrt b)) ^ 2 / 2)
    (Measure.pi (fun _ : Fin N ↦ R.prod (codedLaw μ ν t))).real
        {x | {u | x ∈ accept (N := N) s u c} ≠ ({s} : Set (Residues q k))} ≤
      (q : ℝ)^k * Real.exp (-(N : ℝ) * c^2 / 8) :=
  coded_recovery μ ν t s R hR ha hc he (residual_symmetric_real ν t hs) hμ
    (box_residual_lower ν t tl htl hT hB hν)

end SigabaNeo.Lattices.Attacks.Bkw

#print axioms SigabaNeo.Lattices.Attacks.Bkw.box_residual_lower
#print axioms SigabaNeo.Lattices.Attacks.Bkw.coded_box_recovery

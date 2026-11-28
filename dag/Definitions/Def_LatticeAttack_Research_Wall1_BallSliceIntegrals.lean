import Definitions.Def_LatticeAttack_Research_Wall1_BallSliceTonelli
import Definitions.Def_LatticeAttack_Research_Wall1_BallSliceVolume
import Definitions.Def_LatticeAttack_Research_Wall1_BallSliceFibers

set_option autoImplicit true

/-! Exact radial slice integrals, obtained from volumes rather than special functions. -/
noncomputable section
namespace SigabaNeo.Wall1.RawBallRounding
open Finset MeasureTheory

lemma sliceBall_section (n k : ℕ) (a : ℝ) (x : Fin n → ℝ) :
    Prod.mk x ⁻¹' sliceBall n k a = openEnergySection k (a^2 - ∑ i, (x i)^2) := by
  ext y
  simp only [Set.mem_preimage, sliceBall, openEnergySection, Set.mem_setOf_eq]
  constructor <;> intro h <;> linarith

theorem quadratic_slice_integral (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : Fin n → ℝ, Real.pi * max (a^2 - ∑ i, (x i)^2) 0) =
      unitVolume (n+2) * a^(n+2) := by
  have h := integral_section_volume (measurableSet_sliceBall n 2 a)
    (volume_sliceBall_lt_top n 2 ha).ne
  simp_rw [sliceBall_section, realVolume_openEnergySection_two] at h
  exact h.trans (real_volume_sliceBall n 2 (by omega) ha)

theorem sqrt_slice_integral (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : Fin n → ℝ, 2 * Real.sqrt (max (a^2 - ∑ i, (x i)^2) 0)) =
      unitVolume (n+1) * a^(n+1) := by
  have h := integral_section_volume (measurableSet_sliceBall n 1 a)
    (volume_sliceBall_lt_top n 1 ha).ne
  simp_rw [sliceBall_section, realVolume_openEnergySection_one] at h
  exact h.trans (real_volume_sliceBall n 1 (by omega) ha)

theorem quadratic_slice_integrable (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun x : Fin n → ℝ ↦ Real.pi * max (a^2 - ∑ i, (x i)^2) 0) := by
  have h := Measure.integrable_measure_prodMk_left (measurableSet_sliceBall n 2 a)
    (volume_sliceBall_lt_top n 2 ha).ne
  simpa only [sliceBall_section, realVolume_openEnergySection_two] using h

theorem sqrt_slice_integrable (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun x : Fin n → ℝ ↦ 2 * Real.sqrt (max (a^2 - ∑ i, (x i)^2) 0)) := by
  have h := Measure.integrable_measure_prodMk_left (measurableSet_sliceBall n 1 a)
    (volume_sliceBall_lt_top n 1 ha).ne
  simpa only [sliceBall_section, realVolume_openEnergySection_one] using h

end SigabaNeo.Wall1.RawBallRounding
#print axioms SigabaNeo.Wall1.RawBallRounding.quadratic_slice_integral
#print axioms SigabaNeo.Wall1.RawBallRounding.sqrt_slice_integral
#print axioms SigabaNeo.Wall1.RawBallRounding.quadratic_slice_integrable
#print axioms SigabaNeo.Wall1.RawBallRounding.sqrt_slice_integrable

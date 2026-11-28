import Definitions.Def_LatticeAttack_Research_Wall1_RawCenteredBallEquiv

set_option autoImplicit true

/-! Geometric upper bounds on centered candidate input fibers and total cardinality. -/
noncomputable section
namespace SigabaNeo.Wall1.CenteredPrefixOccupancy
open Finset RawPrefixOccupancy RawBallRounding ControlledPlane DualExit

/-- With the input fixed, projection to outputs is injective and lies in the radius ball. -/
theorem centeredBall_inputFiber_upper (k : ℕ) (R : ℝ) (s : Fin k → ℤ) :
    (((centeredBall k R).filter fun z ↦ z.2 = s).card : ℝ) ≤
      2 * Real.sqrt (R^2 + (400 : ℝ)/4)^400 * unitVolume 400 := by
  let T := (centeredBall k R).filter fun z ↦ z.2 = s
  have hinj : Set.InjOn (fun z : Candidate k ↦ z.1) (T : Set (Candidate k)) := by
    intro z hz w hw he
    apply Prod.ext he
    exact (mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm
  have hcard : (T.image (fun z ↦ z.1)).card = T.card := card_image_of_injOn hinj
  have henergy : ∀ u ∈ T.image (fun z ↦ z.1), ∑ i, (u i : ℝ)^2 ≤ R^2 := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hu
    have hzball := (mem_centeredBall R z).mp (mem_filter.mp hz).1
    have hn : 0 ≤ sqLength z.2 := sum_nonneg fun i _ ↦ sq_nonneg _
    change sqLength z.1 ≤ R^2
    linarith [hzball.2.2]
  have h := inward_half_cube (T.image (fun z ↦ z.1)) R henergy
  rw [hcard] at h
  have hh : (T.card : ℝ)/2 ≤
      Real.sqrt (R^2 + (400 : ℝ)/4)^400 * unitVolume 400 := by
    simpa only [inwardVolume, Fintype.card_fin, unitVolume, Nat.cast_ofNat] using h
  change (T.card : ℝ) ≤ _
  linarith

/-- The same inward-half-cube bound controls the entire centered candidate ball. -/
theorem centeredBall_total_upper (k : ℕ) (R : ℝ) :
    ((centeredBall k R).card : ℝ) ≤
      2 * Real.sqrt (R^2 + ((400+k : ℕ) : ℝ)/4)^(400+k) * unitVolume (400+k) := by
  let e := (Fin.appendEquiv (α := ℤ) 400 k).toEmbedding
  let T := (centeredBall k R).map e
  have henergy : ∀ z ∈ T, ∑ i, (z i : ℝ)^2 ≤ R^2 := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := mem_map.mp hz
    have hh := ((mem_centeredBall R w).mp hw).2.2
    simpa [e, Fin.appendEquiv, Fin.sum_univ_add, sqLength] using hh
  have h := inward_half_cube T R henergy
  have hcard : T.card = (centeredBall k R).card := card_map e
  rw [hcard] at h
  have hh : ((centeredBall k R).card : ℝ)/2 ≤
      Real.sqrt (R^2 + ((400+k : ℕ) : ℝ)/4)^(400+k) * unitVolume (400+k) := by
    simpa only [inwardVolume, Fintype.card_fin, unitVolume] using h
  linarith

end SigabaNeo.Wall1.CenteredPrefixOccupancy
#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.centeredBall_inputFiber_upper
#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.centeredBall_total_upper

import Definitions.Def_LatticeAttack_Research_Wall1_RawBallCount
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit true

/-! Product-coordinate descriptions of Euclidean ball volume. -/
noncomputable section
namespace SigabaNeo.Wall1.RawBallRounding
open Finset Real MeasureTheory Metric
open scoped Classical

/-- The open Euclidean ball written in two groups of real coordinates. -/
def sliceBall (n k : ℕ) (a : ℝ) : Set ((Fin n → ℝ) × (Fin k → ℝ)) :=
  {p | (∑ i, p.1 i ^ 2) + (∑ j, p.2 j ^ 2) < a ^ 2}

lemma measurableSet_sliceBall (n k : ℕ) (a : ℝ) : MeasurableSet (sliceBall n k a) := by
  unfold sliceBall
  exact measurableSet_lt (by fun_prop) measurable_const

private def joinCoords (n k : ℕ) :
    ((Fin n → ℝ) × (Fin k → ℝ)) → (Fin (n+k) → ℝ) :=
  fun p ↦ (MeasurableEquiv.piCongrLeft (fun _ : Fin (n+k) ↦ ℝ) finSumFinEquiv)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin k ↦ ℝ)).symm p)

private lemma joinCoords_preserving (n k : ℕ) : MeasurePreserving (joinCoords n k) := by
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin (n+k) ↦ ℝ)
    finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin k ↦ ℝ))

private lemma joinCoords_energy (n k : ℕ) (p : (Fin n → ℝ) × (Fin k → ℝ)) :
    ∑ i, (joinCoords n k p i)^2 = (∑ i, p.1 i^2) + (∑ j, p.2 j^2) := by
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp only [joinCoords, MeasurableEquiv.piCongrLeft_apply_apply, Fintype.sum_sum_type]
  rfl

/-- Product-coordinate and Euclidean descriptions have the same ball measure. -/
theorem volume_sliceBall (n k : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    volume (sliceBall n k a) = volume (ball (0 : EuclideanSpace ℝ (Fin (n+k))) a) := by
  let f := fun p : (Fin n → ℝ) × (Fin k → ℝ) ↦
    (WithLp.toLp 2 (joinCoords n k p) : EuclideanSpace ℝ (Fin (n+k)))
  have hf : MeasurePreserving f := (PiLp.volume_preserving_toLp _).comp
    (joinCoords_preserving n k)
  have hset : f ⁻¹' ball 0 a = sliceBall n k a := by
    ext p
    simp only [Set.mem_preimage, EuclideanSpace.ball_zero_eq a ha, Set.mem_ofPred_eq]
    change (∑ i, (joinCoords n k p i)^2) < a^2 ↔
      (∑ i, p.1 i^2) + (∑ j, p.2 j^2) < a^2
    rw [joinCoords_energy]
  rw [← hset]
  exact hf.measure_preimage measurableSet_ball.nullMeasurableSet

lemma volume_sliceBall_lt_top (n k : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    volume (sliceBall n k a) < ⊤ := by
  rw [volume_sliceBall n k ha]
  exact measure_ball_lt_top

/-- The real volume of a positive-dimensional sliced ball, including radius zero. -/
theorem real_volume_sliceBall (n k : ℕ) (hnk : 0 < n+k) {a : ℝ} (ha : 0 ≤ a) :
    volume.real (sliceBall n k a) = unitVolume (n+k) * a^(n+k) := by
  let : Nonempty (Fin (n+k)) := ⟨⟨0, hnk⟩⟩
  rw [Measure.real, volume_sliceBall n k ha]
  change volume.real (ball (0 : EuclideanSpace ℝ (Fin (n+k))) a) = _
  rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball,
    Measure.addHaar_real_closedBall volume _ ha, finrank_euclideanSpace_fin]
  exact mul_comm _ _

end SigabaNeo.Wall1.RawBallRounding

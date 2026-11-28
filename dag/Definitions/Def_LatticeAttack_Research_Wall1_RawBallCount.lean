import Definitions.Def_LatticeAttack_Research_Wall1_RawBallRounding

set_option autoImplicit true

/-! Absolute ball counts, including the origin, and their coordinate exclusions. -/
noncomputable section
namespace SigabaNeo.Wall1.RawBallRounding
open Finset Real MeasureTheory Metric DualExit
open scoped Classical

def unitVolume (n : ℕ) := volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1)

def energy (z : Fin n → ℤ) : ℝ := ∑ i, (z i : ℝ)^2

def closedLifts (n : ℕ) (r : ℝ) : Finset (Fin n → ℤ) :=
  insert 0 (SigabaNeo.Planted.integerBall r)

lemma mem_closedLifts {r : ℝ} (hr : 0 ≤ r) (z : Fin n → ℤ) :
    z ∈ closedLifts n r ↔ energy z ≤ r^2 := by
  by_cases hz : z = 0
  · simp [closedLifts,hz,energy,sq_nonneg]
  · simp [closedLifts,SigabaNeo.Planted.mem_integerBall hr,hz,energy]

/-- The full integer ball inherits the integrated rounding lower bound. -/
theorem closedLifts_lower (hn : n ≤ 558) (hr : 1690 ≤ r) :
    (r-7/5)^n * unitVolume n * (119/144) ≤ (closedLifts n r).card := by
  let D := WithLp.toLp 2 ⁻¹' closedBall (0 : EuclideanSpace ℝ (Fin n)) (r-7/5)
  have hD : MeasurableSet D := measurableSet_closedBall.preimage (PiLp.volume_preserving_toLp _).measurable
  have vol : volume D = volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (r-7/5)) :=
    (PiLp.volume_preserving_toLp _).measure_preimage measurableSet_closedBall.nullMeasurableSet
  have hv : volume.real D = (r-7/5)^n * unitVolume n := by
    rw [Measure.real, vol]
    change volume.real _ = _
    rw [Measure.addHaar_real_closedBall volume _ (by linarith), finrank_euclideanSpace_fin]
    rfl
  rw [← hv]
  apply interpolation_count hn hr D hD (vol ▸ measure_closedBall_lt_top.ne)
  · intro x hx
    change dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) 0 ≤ _ at hx
    rw [dist_zero_right] at hx
    simpa only [EuclideanSpace.real_norm_sq_eq] using pow_le_pow_left₀ (norm_nonneg _) hx 2
  · intro x hx b hb
    exact (mem_closedLifts (by linarith) _).2 hb

private lemma upper {T : Finset (Fin n → ℤ)} {s : ℝ} (ht : ∀ z ∈ T, energy z ≤ s^2) :
    (T.card:ℝ) ≤ 2 * sqrt (s^2 + n/4)^n * unitVolume n := by
  have h := inward_half_cube T s ht
  simp only [inwardVolume,Fintype.card_fin] at h
  dsimp [unitVolume]
  linarith

/-- Dropping a coordinate identifies the zero slice with a subset of the lower-dimensional ball. -/
theorem zero_slice_upper (p : Fin (n+1)) {r : ℝ} (hr : 0 ≤ r) :
    (((closedLifts (n+1) r).filter fun z ↦ z p = 0).card : ℝ) ≤
      2 * sqrt (r^2 + n/4)^n * unitVolume n := by
  let T := (closedLifts (n+1) r).filter fun z ↦ z p = 0
  let f (z : Fin (n+1) → ℤ) (i : Fin n) := z (p.succAbove i)
  have hin : Set.InjOn f T := by
    intro z hz w hw he
    funext i
    by_cases hi : i = p
    · simp [hi,(mem_filter.mp hz).2,(mem_filter.mp hw).2]
    · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hi
      exact congrFun he k
  change (T.card:ℝ) ≤ _
  rw [← card_image_of_injOn hin]
  apply upper
  intro w hw
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
  obtain ⟨hb,hp⟩ := mem_filter.mp hz
  have h := (mem_closedLifts hr z).1 hb
  unfold energy at h
  rw [Fin.sum_univ_succAbove _ p] at h
  simpa only [f,energy,hp,Int.cast_zero,zero_pow (by decide : 2 ≠ 0),zero_add] using h

/-- Translating a one-sided coordinate cap by an integer vector bounds its count by a
smaller ball of the same dimension. -/
theorem cap_upper (p : Fin n) (sign : Bool) {r : ℝ} (hr : 1690 ≤ r) :
    (((closedLifts n r).filter fun z ↦ 1664 ≤ (if sign then z p else -z p)).card : ℝ) ≤
      2 * sqrt (r^2 - 1664^2 + n/4)^n * unitVolume n := by
  let d : ℤ := if sign then 1664 else -1664
  let f (z : Fin n → ℤ) := z - Pi.single p d
  let T := (closedLifts n r).filter fun z ↦ 1664 ≤ (if sign then z p else -z p)
  have hin : Function.Injective f := fun _ _ h ↦ sub_left_injective h
  change (T.card:ℝ) ≤ _
  rw [← card_image_of_injOn (s := T) hin.injOn]
  have hrad : 0 ≤ r^2 - 1664^2 := by nlinarith
  have hu := @upper n (T.image f) (sqrt (r^2 - 1664^2))
  rw [sq_sqrt hrad] at hu
  apply hu
  intro w hw
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
  have hb := (mem_closedLifts (by linarith : 0 ≤ r) z).1 (mem_filter.mp hz).1
  have hc := (mem_filter.mp hz).2
  have he : energy (f z) = energy z - (z p:ℝ)^2 + ((z p:ℝ) - d)^2 := by
    unfold energy
    rw [← add_sum_erase _ _ (mem_univ p), ← add_sum_erase _ (fun i ↦ (z i:ℝ)^2) (mem_univ p)]
    have hs : ∀ i ∈ univ.erase p, f z i = z i := fun i hi ↦ by
      simp [f,Pi.single_eq_of_ne (ne_of_mem_erase hi)]
    rw [sum_congr rfl (fun i hi ↦ congrArg (fun t : ℤ ↦ (t:ℝ)^2) (hs i hi))]
    simp [f]
    ring
  rw [he]
  cases sign <;> simp only [Bool.false_eq_true, ite_false, ite_true, d, Int.cast_neg,
    Int.cast_ofNat] at hc ⊢
  · have h' : (1664:ℝ) ≤ -(z p:ℝ) := by exact_mod_cast hc
    linarith
  · have h' : (1664:ℝ) ≤ (z p:ℝ) := by exact_mod_cast hc
    linarith

end SigabaNeo.Wall1.RawBallRounding
#print axioms SigabaNeo.Wall1.RawBallRounding.closedLifts_lower
#print axioms SigabaNeo.Wall1.RawBallRounding.zero_slice_upper
#print axioms SigabaNeo.Wall1.RawBallRounding.cap_upper

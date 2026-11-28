import Definitions.Def_LatticeAttack_Research_Wall1_RawInputFiberBound
import Definitions.Def_LatticeAttack_Research_Wall1_RawPairCollision

set_option autoImplicit true

/-! Centered input representatives preserve fiber bounds under reduction modulo3329. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane QaryMembership
open scoped Classical

/-- Reduction is injective on the centered integer input cube. -/
theorem centered_reduce_injective {k : ℕ} (s t : Fin k → ℤ)
    (hs : ∀ i, -1664 ≤ s i ∧ s i ≤ 1664)
    (ht : ∀ i, -1664 ≤ t i ∧ t i ≤ 1664)
    (he : reduce 3329 s = reduce 3329 t) : s = t := by
  funext i
  exact centered_intCast_injective (hs i) (ht i) (congrFun he i)

/-- Every nonempty residue fiber is exactly an integer input fiber. -/
theorem reduced_input_fiber_bound {k : ℕ} (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ s, ((T.filter fun z ↦ z.2 = s).card : ℝ) ≤ B)
    (y : Fin k → ZMod 3329) :
    ((T.filter fun z ↦ reduce 3329 z.2 = y).card : ℝ) ≤ B := by
  by_cases hn : (T.filter fun z ↦ reduce 3329 z.2 = y).Nonempty
  · obtain ⟨w, hw⟩ := hn
    have hwT := (mem_filter.mp hw).1
    have hwy := (mem_filter.mp hw).2
    have he : (T.filter fun z ↦ reduce 3329 z.2 = y) =
        T.filter fun z ↦ z.2 = w.2 := by
      apply filter_congr
      intro z hz
      constructor
      · intro hzy
        exact centered_reduce_injective _ _ (hT z hz) (hT w hwT) (hzy.trans hwy.symm)
      · intro he
        simpa only [he] using hwy
    rw [he]
    exact hB w.2
  · rw [not_nonempty_iff_eq_empty.mp hn]
    simpa only [card_empty, Nat.cast_zero] using hB0

end SigabaNeo.Wall1.RawPrefixOccupancy
namespace SigabaNeo.Wall1.CenteredPrefixOccupancy
open RawPrefixOccupancy RawBallRounding QaryMembership

/-- The geometric fiber estimate also holds for every residue-class input. -/
theorem centeredBall_reduced_inputFiber_upper (k : ℕ) (R : ℝ)
    (y : Fin k → ZMod 3329) :
    (((centeredBall k R).filter fun z ↦ reduce 3329 z.2 = y).card : ℝ) ≤
      2 * Real.sqrt (R^2 + (400 : ℝ)/4)^400 * unitVolume 400 := by
  apply reduced_input_fiber_bound (centeredBall k R)
    (fun z hz ↦ ((mem_centeredBall R z).mp hz).2.1)
  · unfold unitVolume
    positivity
  · exact centeredBall_inputFiber_upper k R

end SigabaNeo.Wall1.CenteredPrefixOccupancy
#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.centeredBall_reduced_inputFiber_upper

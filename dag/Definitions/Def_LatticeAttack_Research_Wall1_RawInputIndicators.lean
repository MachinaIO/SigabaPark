import Definitions.Def_LatticeAttack_Research_Wall1_RawPairCollision
import Definitions.Def_LatticeAttack_Research_Wall1_FactorialMomentGeneratingSeries

set_option autoImplicit true

/-! Raw counts are sums of input-fiber indicators, with their joint law retained. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane TerminalProjection FactorialMomentTransfer
open scoped Classical

/-- The input fiber contains a candidate with the given raw syndrome. -/
def inputHit {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (A : Sample) (c : Column) (s : Fin k → ℤ) : Prop :=
  ∃ z ∈ T, z.2 = s ∧ rawSyndrome hk A z = c

/-- A centered output fiber contributes at most one candidate to each raw label. -/
theorem input_injOn_raw_fiber {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664)
    (A : Sample) (c : Column) :
    Set.InjOn Prod.snd (↑(T.filter fun z ↦ rawSyndrome hk A z = c) : Set (Candidate k)) := by
  intro z hz w hw hin
  obtain ⟨hzT, hzc⟩ := mem_filter.mp hz
  obtain ⟨hwT, hwc⟩ := mem_filter.mp hw
  apply Prod.ext _ hin
  by_contra hout
  exact rawSyndrome_ne_of_same_input hk A z w (hT z hzT) (hT w hwT) hin hout
    (hzc.trans hwc.symm)

theorem rawCount_eq_inputHit_card {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664)
    (A : Sample) (c : Column) :
    rawCount hk T A c = ((T.image Prod.snd).filter (inputHit hk T A c)).card := by
  rw [rawCount_eq_fiber, ← card_image_of_injOn (input_injOn_raw_fiber hk T hT A c)]
  apply congrArg Finset.card
  ext s
  simp only [mem_image, mem_filter, inputHit]
  aesop

/-- A pointwise product of indicators, not a product of their expectations. -/
theorem raw_generating_product {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664)
    (A : Sample) (c : Column) :
    (1 + PowerSeries.X : PowerSeries ℝ)^(rawCount hk T A c) =
      ∏ s ∈ T.image Prod.snd,
        if inputHit hk T A c s then (1 + PowerSeries.X : PowerSeries ℝ) else 1 := by
  rw [rawCount_eq_inputHit_card hk T hT]
  rw [← prod_filter]
  simp only [prod_const]

/-- The actual factorial generating series is the joint average of input-fiber
products. This equality makes no independence claim about those indicators. -/
theorem raw_factorial_series_input_product {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664) :
    normalizedMomentSeries (factorialAverage (rawCount hk T)) =
      (((Fintype.card Sample : ℝ) * Fintype.card Column)⁻¹) •
        (∑ A, ∑ c, ∏ s ∈ T.image Prod.snd,
          if inputHit hk T A c s then (1 + PowerSeries.X : PowerSeries ℝ) else 1) := by
  rw [normalizedMomentSeries_factorialAverage]
  simp_rw [raw_generating_product hk T hT]

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.rawCount_eq_inputHit_card
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_factorial_series_input_product

import Definitions.Def_LatticeAttack_Research_Wall1_RawInputIndicators
import Definitions.Def_LatticeAttack_Research_Wall1_OrderedFiberTuples

set_option autoImplicit true

/-! Simultaneous input hits have a unique ordered candidate witness. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane TerminalProjection OrderedFiberTuples
open scoped Classical

theorem input_hits_iff_unique_tuple {k h : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k))
    (hout : ∀ z ∈ T, ∀ j, -1664 ≤ z.1 j ∧ z.1 j ≤ 1664)
    (s : Fin h → Fin k → ℤ) (hs : Function.Injective s) (A : Sample) (c : Column) :
    (∀ i, inputHit hk T A c (s i)) ↔
      ∃! e : orderedTuples T h, ∀ i, (e i).val.2 = s i ∧ rawSyndrome hk A (e i).val = c := by
  constructor
  · intro hh
    choose z hz hin hhit using hh
    let e : orderedTuples T h :=
      ⟨fun i ↦ ⟨z i, hz i⟩, fun i j hij ↦ hs (by
        have he := congrArg (fun x : T ↦ x.val.2) hij
        simpa only [hin] using he)⟩
    refine ⟨e, fun i ↦ ⟨hin i, hhit i⟩, ?_⟩
    intro f hf
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact input_injOn_raw_fiber hk T hout A c
      (mem_filter.mpr ⟨(f i).property, (hf i).2⟩)
      (mem_filter.mpr ⟨hz i, hhit i⟩) ((hf i).1.trans (hin i).symm)
  · rintro ⟨e, he, _⟩ i
    exact ⟨(e i).val, (e i).property, (he i).1, (he i).2⟩

theorem input_hits_indicator_eq_tuple_sum {k h : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k))
    (hout : ∀ z ∈ T, ∀ j, -1664 ≤ z.1 j ∧ z.1 j ≤ 1664)
    (s : Fin h → Fin k → ℤ) (hs : Function.Injective s) (A : Sample) (c : Column) :
    (if ∀ i, inputHit hk T A c (s i) then (1 : ℝ) else 0) =
      ∑ e : orderedTuples T h,
        if ∀ i, (e i).val.2 = s i ∧ rawSyndrome hk A (e i).val = c then 1 else 0 := by
  by_cases hh : ∀ i, inputHit hk T A c (s i)
  · obtain ⟨e, he, hu⟩ := (input_hits_iff_unique_tuple hk T hout s hs A c).mp hh
    have hiff (f : orderedTuples T h) :
        (∀ i, (f i).val.2 = s i ∧ rawSyndrome hk A (f i).val = c) ↔ f = e :=
      ⟨fun hf ↦ hu f hf, fun hf ↦ hf ▸ he⟩
    simp only [hh, hiff]
    simp
  · rw [ite_eq_right hh]
    symm
    apply sum_eq_zero
    intro e _
    apply ite_eq_right
    intro he
    exact hh (fun i ↦ ⟨(e i).val, (e i).property, (he i).1, (he i).2⟩)

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.input_hits_indicator_eq_tuple_sum

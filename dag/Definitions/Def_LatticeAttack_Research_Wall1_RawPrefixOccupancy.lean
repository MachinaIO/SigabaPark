import Definitions.Def_LatticeAttack_Research_Wall1_RawGraphWitness
import Definitions.Def_LatticeAttack_Research_Wall1_CommonRawWitness

set_option autoImplicit true

/-! # A fixed raw prefix and the actual retained marked groups

Finite raw candidate counts are connected to the actual restart's marked cosets.
Coverage means existence of a representative in the closed radius ball; its binary
occupancy has exactly the desired empty labels. No candidate distribution or numerical
moment bound is assumed here. The final theorem needs the raw first moment as an input
to obtain a numerical probability estimate.
-/

noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset Submodule ControlledPlane TerminalProjection TerminalProjection.Restart506
open LongWinner.FourthMoment CommonRawWitness CosetOccupancy
open scoped Classical

def StateMark (A : Sample) (j : ℕ) :=
  Marks (retained (history A) j).M
    (markedPreimage (retained (history A) j).M (retained (history A) j).g)

instance stateMarkAddCommGroup (A : Sample) (j : ℕ) : AddCommGroup (StateMark A j) :=
  inferInstanceAs (AddCommGroup (Marks (retained (history A) j).M
    (markedPreimage (retained (history A) j).M (retained (history A) j).g)))

def stateMark (A : Sample) (j : ℕ) : Column →+ StateMark A j :=
  columnMark _ _ (retained (history A) j).periods

theorem stateMark_surjective (A : Sample) (j : ℕ) : Function.Surjective (stateMark A j) :=
  columnMark_surjective _ _ _

instance stateMarkFintype (A : Sample) (j : ℕ) : Fintype (StateMark A j) := by
  letI := Finite.of_surjective (stateMark A j) (stateMark_surjective A j)
  exact Fintype.ofFinite _

theorem stateMark_uniform (A : Sample) (j : ℕ) (y : StateMark A j) :
    (univ.filter fun c ↦ stateMark A j c = y).card = Fintype.card (stateMark A j).ker :=
  uniform_fibers_of_surjective (stateMark A j) (stateMark_surjective A j) y

/-- Binary occupancy of the actual marked coset in a closed ball. -/
def occupied (A : Sample) (j : ℕ) (r : ℝ) (c : StateMark A j) : ℕ :=
  if ∃ z : CoordSpace 505, ‖z‖ ≤ r ∧ (retained (history A) j).M.mkQ z = c.val
  then 1 else 0

abbrev Candidate (k : ℕ) := (Fin 400 → ℤ) × (Fin k → ℤ)

/-- Number of fixed integer prefix candidates having the given raw syndrome. -/
def rawCount {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (A : Sample) (c : Column) : ℕ :=
  (T.filter fun z ↦ ∀ i, (z.1 i : ZMod 3329) = c i +
    ∑ t, (z.2 t : ZMod 3329) * A i (t.castLE hk)).card

/-- Each raw hit gives an actual short marked-coset representative at every later entry. -/
theorem preserves_raw_hit {k j : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (hj : j ≤ 406) (hprefix : k ≤ 105+j) {r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R)
    (hshort : ∀ z ∈ T, sqLength z.1 + sqLength z.2 ≤ r^2)
    (A : Sample) (c : Column) (hhit : rawCount hk T A c ≠ 0) :
    occupied A j R (stateMark A j c) ≠ 0 := by
  obtain ⟨z, hz⟩ := card_pos.mp (Nat.pos_of_ne_zero hhit)
  obtain ⟨hzT, hzc⟩ := mem_filter.mp hz
  obtain ⟨w, hw, hclass⟩ := retained_coset_representative_of_prefix A hj hprefix
    z.1 z.2 (fun i ↦ ((c i).val : ℤ))
    (by simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hzc) hr (hshort z hzT)
  have hrepr : (∑ i, ((c i).val : ℤ) • (retained (history A) j).g i) =
      columnLift (retained (history A) j).g c := by
    simp only [columnLift, natCast_zsmul]
  rw [hrepr] at hclass
  have hcovered : ∃ w : CoordSpace 505, ‖w‖ ≤ R ∧
      (retained (history A) j).M.mkQ w = (stateMark A j c).val :=
    ⟨w, hw.trans hR, hclass.trans (columnMark_repr _ _ _ c)⟩
  simp only [occupied, ite_eq_left hcovered, ne_eq, one_ne_zero, not_false_eq_true]

/-- One raw first moment controls all eligible actual retained-state exits together.
The raw matrix is never conditioned on the history or on its radius gate. -/
theorem actual_history_exit_first_moment {ι : Type*} {k : ℕ}
    (hk : k ≤ 512) (T : Finset (Candidate k)) (time : ι → ℕ)
    (htime : ∀ i, time i ≤ 406) (hprefix : ∀ i, k ≤ 105+time i)
    {r : ℝ} (hr : 0 ≤ r) (hshort : ∀ z ∈ T, sqLength z.1 + sqLength z.2 ≤ r^2)
    (radius : ι → Sample → ℝ) (a b : ℕ) :
    a * Fintype.card Column *
      (univ.filter fun A ↦ ∃ i, r ≤ radius i A ∧
        a * Fintype.card (StateMark A (time i)) ≤
          b * emptyCount (occupied A (time i) (radius i A))).card ≤
    b * ∑ A, emptyCount (rawCount hk T A) := by
  apply quotient_history_exit_first_moment (rawCount hk T)
    (fun i A ↦ occupied A (time i) (radius i A))
    (fun i A ↦ stateMark A (time i))
    (fun i A ↦ Fintype.card (stateMark A (time i)).ker)
    (fun i A y ↦ stateMark_uniform A (time i) y)
    (fun i A ↦ r ≤ radius i A)
  intro i A hR c hc
  exact preserves_raw_hit hk T (htime i) (hprefix i) hr hR hshort A c hc

end SigabaNeo.Wall1.RawPrefixOccupancy

#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.stateMark_surjective
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.stateMark_uniform
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.preserves_raw_hit
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.actual_history_exit_first_moment

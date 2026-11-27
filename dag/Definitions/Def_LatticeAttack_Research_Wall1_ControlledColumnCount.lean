import Definitions.Def_LatticeAttack_Research_Wall1_ControlledPlaneGeometry
import Definitions.Def_LatticeAttack_Research_Wall1_ConcreteTerminal506

set_option autoImplicit true

/-! The unconditioned fresh-column test on a fixed retained or forced-old state.
At old rank 505 the projected-grid counting theorem gives a closed radial bound. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open TerminalProjection TerminalProjection.Restart506 Submodule Module MeasureTheory

variable {n d : ℕ}
private abbrev K (s : ChainState n (CoordSpace d)) := markedPreimage s.M s.g
private abbrev mark (s : ChainState n (CoordSpace d)) := columnMark s.M s.g s.periods

private theorem old_le (s : ChainState n (CoordSpace d)) : s.M ≤ K s := by
  unfold K
  rw [markedPreimage_eq]
  exact le_sup_left

local instance (s : ChainState n (CoordSpace d)) : Fintype (Marks s.M (K s)) := by
  letI := Finite.of_surjective (mark s) (columnMark_surjective s.M s.g s.periods)
  exact Fintype.ofFinite _

local instance (s : ChainState n (CoordSpace d)) : DiscreteTopology (K s) :=
  markedPreimage_discrete _ _ _ s.periods (by decide)

local instance (s : ChainState n (CoordSpace d)) : IsZLattice ℝ (K s) := ⟨top_unique <|
  (IsZLattice.span_top (K := ℝ) (L := s.M)).ge.trans (span_mono (old_le s))⟩

/-- A ratio independent of the choice of representatives of the finite mark group. -/
def candidateRatio (s : ChainState n (CoordSpace d)) (r : ℝ) : ℝ :=
  (TerminalProjection.candidates (K s) r).card / (Fintype.card (Marks s.M (K s)) : ℝ)

theorem column_positive_bound (s : ChainState n (CoordSpace d)) {r : ℝ} (hr : r < 3329) :
    mass (fun c : Column ↦ PositiveHit s.M (columnLift s.g c) r) ≤ candidateRatio s r := by
  let f := mark s
  have onto : Function.Surjective f := columnMark_surjective s.M s.g s.periods
  let raw := fun z ↦ (onto z).choose
  exact fresh_column_probability s.M (K s) (fun z ↦ columnLift s.g (raw z))
    f onto _ (columnMark_repr s.M s.g s.periods) (by norm_num : Nat.Prime 3329)
    (fun _ hw ↦ torsion_preimage _ _ s.periods hw) (old_le s) (fun _ ↦ columnLift_mem ..)
    (fun z ↦ (columnMark_repr ..).trans (congrArg Subtype.val (onto z).choose_spec))
    (by exact_mod_cast hr)

private theorem realization (s : ChainState n (CoordSpace d)) :
    projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin (n+1)) ℝ)))
        s.frame.append.space = transport s.frame.append.embed (appendWindow (K s) 0) := by
  rw [transport_eq, AxisFrame.grid_eq, AxisFrame.integerSpan_append, ← s.marked]

/-- Applies at every index before the next column is read. -/
theorem candidateRatio_505 (s : ChainState n (CoordSpace 505)) {r : ℝ} (hr : 0 < r) :
    candidateRatio s r ≤ countingConstantAt (r * Real.sqrt (2*Real.pi/506)) *
      (r/terminalScale (ZLattice.covolume s.M))^506 := by
  let frame := s.frame.append
  let G := projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin (n+1)) ℝ))) frame.space
  let : DiscreteTopology (appendWindow (K s) 0) := (appendWindow_lattice _ _).choose
  let : IsZLattice ℝ (appendWindow (K s) 0) := (appendWindow_lattice _ _).choose_spec
  have he : G = transport frame.embed (appendWindow (K s) 0) := realization s
  let : DiscreteTopology G := he ▸ inferInstanceAs (DiscreteTopology (transport _ (appendWindow (K s) 0)))
  let : IsZLattice ℝ G := ⟨by rw [he]; exact IsZLattice.span_top⟩
  apply projected_candidates_count s.M (K s) frame.space _ frame.embed.toLinearIsometry _ _ r hr
  · rw [← frame.embed.toLinearEquiv.finrank_eq, (WithLp.linearEquiv 2 ℝ _).finrank_eq,
      Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
  · intro w hw
    rw [realization, transport_eq]
    exact ⟨w,hw,rfl⟩
  · rw [realization, transport_covolume, covolume_append, marks_mul_covolume _ _ (old_le s)]

/-- Nonzero height is oriented after the actual signed winner comparison. Both
signs have the same norm and belong to the window. -/
theorem column_winner_bound (s : ChainState n (CoordSpace 505)) {r : ℝ}
    (hr : 0 < r) (hq : r < 3329) :
    mass (fun c : Column ↦ (s.append c).winner.snd ≠ 0 ∧ ‖(s.append c).winner‖ ≤ r) ≤
      countingConstantAt (r * Real.sqrt (2*Real.pi/506)) *
        (r/terminalScale (ZLattice.covolume s.M))^506 := by
  classical
  have incl (c : Column) (h : (s.append c).winner.snd ≠ 0 ∧ ‖(s.append c).winner‖ ≤ r) :
      PositiveHit s.M (columnLift s.g c) r := by
    let w := (s.append c).winner
    have hm : w ∈ appendWindow s.M (columnLift s.g c) := (s.append c).shortest.1
    rcases lt_or_gt_of_ne h.1 with hn | hp
    · exact ⟨-w, (appendWindow _ _).neg_mem hm, by simpa [w] using hn, by simpa [w] using h.2⟩
    · exact ⟨w,hm,hp,h.2⟩
  apply le_trans _ ((column_positive_bound s hq).trans (candidateRatio_505 s hr))
  unfold mass
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (Finset.monotone_filter_right Finset.univ fun c _ ↦ incl c)

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.column_positive_bound
#print axioms SigabaNeo.Wall1.ControlledPlane.candidateRatio_505
#print axioms SigabaNeo.Wall1.ControlledPlane.column_winner_bound

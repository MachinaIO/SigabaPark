import Definitions.Def_LatticeAttack_Research_Wall1_TerminalRestartPath
import Definitions.Def_LatticeAttack_Research_Wall1_RankinSaturation
import Definitions.Def_LatticeAttack_Research_Wall1_ControlledBinaryHermite

set_option autoImplicit true

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open TerminalProjection TerminalProjection.Restart506 DecoupledDecoder
open scoped RealInnerProductSpace

/-- Physical area cutoff and its binary and ternary Hermite length scales. -/
def areaCut : ℝ := 1352 / Real.sqrt 3
def planeRadius : ℝ := Real.sqrt (2 * areaCut / Real.sqrt 3)
def winnerRadius : ℝ := Real.sqrt (Real.sqrt 2 * areaCut)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {L : Submodule ℤ V}

/-- Saturation is relative to the retained lattice, at draw zero or after a freeze. -/
def Hit (h : History) (t : ℕ) : Prop :=
  ∃ b : RankinFamily (retained h t).M 2, b.IsPrimitive ∧
    familyVolume b.vec ≤ ENNReal.ofReal areaCut

theorem hit_shortest (h : History) (t : ℕ) (hit : Hit h t) :
    ‖(retained h t).winner‖ ≤ planeRadius := by
  obtain ⟨b,_,hb⟩ := hit
  obtain ⟨v,hv,hn,hs⟩ := short_in_span b.vec b.ind
  have incl : Submodule.span ℤ (Set.range b.vec) ≤ (retained h t).M :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr b.mem)
  have hwin := (retained h t).shortest.2.2 v (incl hv) hn
  have ha : Real.sqrt (Matrix.gram ℝ b.vec).det ≤ areaCut :=
    (ENNReal.ofReal_le_ofReal_iff (by unfold areaCut; positivity)).mp hb
  apply hwin.trans
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ (by positivity : 0 < Real.sqrt 3)).mpr
  linarith

/-- Numbering of a transition is zero-based here: the winner creates state t+1. -/
def horizontalWinner (h : History) (t : ℕ) : Prop :=
  ((ChainState.windowCoord 505).symm (window h t).winner).snd = 0

def winLength (h : History) (t : ℕ) : ℝ := ‖(window h t).winner‖

/-- On a horizontal win, the newest frame axis measures fresh height also after
freezing. Existence over all shortest vectors includes ties. -/
def freshPlaneShortest (h : History) (t : ℕ) : Prop :=
  let s := retained h (t+1)
  ∃ b : RankinFamily s.M 2, b.IsPrimitive ∧ familyVolume b.vec ≤ ENNReal.ofReal areaCut ∧
    ∃ v, IsShortest (Submodule.span ℤ (Set.range b.vec) : Set (CoordSpace 505)) v ∧
      ⟪s.frame.axis (Fin.last (505+t)), v⟫ ≠ 0

/-- Freeze j designated old winners without reading another column. -/
def forceOld {n d : ℕ} : (j : ℕ) → ChainState n (CoordSpace (d+j)) → ChainState n (CoordSpace d)
  | 0, s => s
  | j+1, s => forceOld j s.freeze

/-- Last used draw i+1, with j old directions skipped. The inner index is
0 ≤ j < 155-i, so both the first and the last allowable flags are included. -/
abbrev FlagIndex := (i : Fin 154) × Fin (155-i.val)

def flagTest (radius logFloor : FlagIndex → ℝ) (idx : FlagIndex) (h : History) : Prop :=
  let i := idx.1.val
  let j := idx.2.val
  have hj : 505 - j + j = 505 := by dsimp [j]; omega
  let s := forceOld (d := 505-j) j (hj ▸ retained h i)
  Real.exp (logFloor idx) ≤ ZLattice.covolume s.M ∧
    PositiveHit s.M (columnLift s.g (past h (105+i))) (radius idx)

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.hit_shortest

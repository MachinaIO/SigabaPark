import Definitions.Def_LatticeAttack_Research_Wall1_TerminalChainState

set_option autoImplicit true

/-! # The width-506 graph restart in physical coordinates

Start with 400 modulus axes, append 105 graph columns before any projection, then append
one column and freeze one signed shortest vector per draw. All independent raw columns
have 400 residues; the ambient frame retains their reveal order across coordinate changes.
-/

noncomputable section
namespace SigabaNeo.Wall1.TerminalProjection.Restart506

open Module Submodule DecoupledDecoder ChainState Blichfeldt

private abbrev axes := EuclideanSpace.basisFun (Fin 400) ℝ

private def scaledBasis : Basis (Fin 400) ℝ (CoordSpace 400) :=
  axes.toBasis.isUnitSMul (w := fun _ ↦ (3329 : ℝ)) (fun _ ↦ isUnit_iff_ne_zero.2 (by norm_num))

private theorem scaled_apply (i : Fin 400) : scaledBasis i = 3329 • axes i := by
  rw [scaledBasis, Basis.isUnitSMul_apply]
  exact_mod_cast (Nat.cast_smul_eq_nsmul ℝ (3329 : ℕ) (axes i))

def initial : ChainState 400 (CoordSpace 400) where
  M := span ℤ (Set.range scaledBasis)
  g := axes
  periods i := scaled_apply i ▸ subset_span (Set.mem_range_self i)
  frame := AxisFrame.ofBasis axes
  marked := by
    rw [markedPreimage_eq]
    apply sup_eq_right.mpr
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [scaled_apply]
    exact (span ℤ (Set.range ⇑axes)).toAddSubmonoid.nsmul_mem (subset_span (Set.mem_range_self i)) _

theorem initial_covolume : ZLattice.covolume initial.M = (3329 : ℝ)^400 := by
  change ZLattice.covolume (span ℤ (Set.range scaledBasis)) = _
  rw [minkowski_covolume_eq_abs_det, Basis.det_apply, scaledBasis, Basis.toMatrix_isUnitSMul,
    Matrix.det_diagonal]
  simp

/-- One unit-height column expressed in coordinates of the enlarged physical space. -/
def incoming {d n : ℕ} (s : ChainState n (CoordSpace d)) (c : Column) :
    ChainState (n+1) (CoordSpace (d+1)) := (s.append c).reframe (windowCoord d)

theorem incoming_covolume {d n : ℕ} (s : ChainState n (CoordSpace d)) (c : Column) :
    ZLattice.covolume (incoming s c).M = ZLattice.covolume s.M := by
  change ZLattice.covolume (transport (windowCoord d) (s.append c).M) = _
  rw [transport_covolume]
  exact covolume_append _ _

theorem incoming_modulus {d n : ℕ} (s : ChainState n (CoordSpace d)) (c : Column) :
    ∃ z ∈ (incoming s c).M, z ≠ 0 ∧ ‖z‖ ≤ 3329 := by
  have ht := torsion_preimage s.M s.g s.periods (columnLift_mem s.M s.g c)
  obtain ⟨z, hz, h0, hq⟩ := modulus_witness s.M (columnLift s.g c) ht (by decide)
  let e := windowCoord d
  exact ⟨e z, (show e.symm (e z) ∈ (s.append c).M by rwa [e.symm_apply_apply]),
    fun he ↦ h0 (e.injective (he.trans (map_zero e).symm)), by simpa using hq⟩

abbrev History := Fin 511 → Column

/-- The path only reads the 511 revealed columns through its 406th projection. -/
def past (h : History) (i : ℕ) : Column := if hi : i < 511 then h ⟨i, hi⟩ else 0

def graphPrefix (h : History) : (t : ℕ) → ChainState (400+t) (CoordSpace (400+t))
  | 0 => initial
  | t+1 => incoming (graphPrefix h t) (past h t)

theorem graphPrefix_covolume (h : History) (t : ℕ) :
    ZLattice.covolume (graphPrefix h t).M = (3329 : ℝ)^400 := by
  induction t with
  | zero => exact initial_covolume
  | succ t ih => exact (incoming_covolume ..).trans ih

def retained (h : History) : (t : ℕ) → ChainState (505+t) (CoordSpace 505)
  | 0 => graphPrefix h 105
  | t+1 => (incoming (retained h t) (past h (105+t))).freeze

def window (h : History) (t : ℕ) := incoming (retained h t) (past h (105+t))

def path (h : History) : WindowPath where
  det t := ZLattice.covolume (retained h t).M (MeasureTheory.volume : MeasureTheory.Measure (CoordSpace 505))
  window i := (window h i.val).M
  winner i := (window h i.val).winner
  shortest i := (window h i.val).shortest
  modulus i := incoming_modulus _ _
  initial := graphPrefix_covolume h 105
  covol i := (incoming_covolume ..).symm
  step i := by
    change ZLattice.covolume (window h i.val).freeze.M = _
    rw [freeze_covolume]
    exact congrArg (fun x ↦ x / _) (incoming_covolume ..)

end SigabaNeo.Wall1.TerminalProjection.Restart506

#print axioms SigabaNeo.Wall1.TerminalProjection.Restart506.initial_covolume
#print axioms SigabaNeo.Wall1.TerminalProjection.Restart506.path

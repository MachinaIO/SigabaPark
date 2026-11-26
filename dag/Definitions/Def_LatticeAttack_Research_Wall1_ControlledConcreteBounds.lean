import Definitions.Def_LatticeAttack_Research_Wall1_ControlledFlagSum
import Definitions.Def_LatticeAttack_Research_Wall1_ControlledFlagDeterminant
import Definitions.Def_LatticeAttack_Research_Wall1_ControlledHorizontalDraw
import Definitions.Def_LatticeAttack_Research_Wall1_ControlledRawCoordinates

set_option autoImplicit true

/-! Part 192 on the concrete chain with the remaining geometry stated explicitly. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open TerminalProjection TerminalProjection.Restart506 DualExit Real
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- Last-used-coordinate alternative for the remaining positive-draw prefix. -/
def LastCoordinateCoverage : Prop :=
  ∀ (A : Sample) (t : ℕ), 0 < t → t ≤ 154 → ‖(retained (history A) t).winner‖ ≤ planeRadius →
    rawShort (designPrefix (by decide : 105 ≤ 512) A) 2885 ∨
    ∃ u, flagTest flagRadius flagFloor u (history A)

/-- Only states preceding draws 22 through 406 need the sharp physical floor. -/
def LaterDeterminantFloor : Prop := ∀ (h : History) (t : Fin 406), 20 < t.val →
  exp (terminalLogFloor t.val) ≤ ZLattice.covolume (retained h t.val).M

private theorem physical_floor (floor : LaterDeterminantFloor) (h : History) (t : Fin 406) :
    exp (terminalLogFloor t.val) ≤ ZLattice.covolume (retained h t.val).M := by
  by_cases ht : t.val ≤ 20
  · exact retained_floor_first20 h _ ht
  · exact floor h t (by omega)

/-- Geometric form of the unresolved prefix construction. In the old branch one
only has to lift a short vector. In the fresh branch the determinant guard and
all candidate counts follow from the preceding results. -/
theorem coverage_of_flag_lifts (floor : LaterDeterminantFloor)
    (lift : ∀ (A : Sample) (t : ℕ), 0 < t → t ≤ 154 →
      ‖(retained (history A) t).winner‖ ≤ planeRadius →
      (∃ w ∈ (retained (history A) 0).M, w ≠ 0 ∧ ‖w‖ ≤ planeRadius * flagCap 155) ∨
      ∃ u : FlagIndex,
        let j := u.2.val
        let k := 155-u.1.val
        have he : 505-j+j = 505 := by dsimp [j]; omega
        let s := Eq.rec (motive := fun a _ ↦ ChainState (a+u.1.val) (CoordSpace a))
          (retained (history A) u.1.val) he.symm
        ForcedLengths (d:=505-j) j k s ∧ PositiveHit (forceOld j s).M
          (columnLift (forceOld j s).g (past (history A) (105+u.1.val))) (flagRadius u)) :
    LastCoordinateCoverage := by
  intro A t ht ht' hs
  obtain ⟨w,hw,hn,hr⟩ | ⟨u,hl,hp⟩ := lift A t ht ht' hs
  · exact Or.inl (rawShort_of_initial_flag 155 le_rfl A hw hn hr)
  · right
    refine ⟨u,flagTest_of_lengths u (history A) ?_ hl hp⟩
    exact (le_log_iff_exp_le (ZLattice.covolume_pos _ _)).2
      (physical_floor floor _ ⟨u.1.val,by omega⟩)

/-- The sharp rank-506 winner inequality suffices for the remaining physical floor. -/
theorem laterFloor_of_hermite
    (cap : ∀ (h : History) (j : ℕ), j < 405 →
      winLength h j ^ 2 ≤ 56.2142 * ZLattice.covolume (retained h j).M ^ (2/(506:ℝ))) :
    LaterDeterminantFloor := by
  intro h t _
  exact retained_floor_of_hermite h t.val (by omega) (fun j hj ↦ cap h j (by omega))

private theorem plane_le : planeRadius ≤ 31 := by
  unfold planeRadius areaCut
  rw [mul_div_assoc',div_div,← sq,sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  exact (sqrt_le_left (by norm_num)).mpr (by norm_num)

theorem concrete_prefix (cover : LastCoordinateCoverage) : PrefixEstimates where
  cover A t ht hs := by
    rcases Nat.eq_zero_or_pos t with rfl | hp
    · have sh := (retained (history A) 0).shortest
      exact Or.inl (rawShort_of_initial A sh.1 sh.2.1 (hs.trans (plane_le.trans (by norm_num))))
    · exact cover A t hp ht hs
  ball := prefix_ball

/-- All three adaptive Gaussian comparisons at the specified Part 192 floor. -/
theorem concrete_late (floor : LaterDeterminantFloor) : LateEstimates := by
  refine ⟨fun A t ↦ hit_winner_cap (history A) t.val,?_,?_,?_⟩
  · intro t
    let i : Fin 406 := ⟨t.val,by omega⟩
    apply positiveCase_gaussian i (by unfold winnerRadius areaCut; positivity) _ (fun h ↦ physical_floor floor h i)
    unfold winnerRadius areaCut
    apply (sqrt_lt' (by norm_num)).mpr
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < sqrt 3)).mpr
    linarith [(sqrt_le_left (by norm_num : (0:ℝ) ≤ 2)).mpr (by norm_num : (2:ℝ) ≤ 2^2),
      le_sqrt_of_sq_le (by norm_num : (1:ℝ)^2 ≤ 3)]
  · intro t
    exact positiveCase_gaussian t (by norm_num) (by norm_num) (fun h ↦ physical_floor floor h t)
  · intro t
    exact horizontalCase_gaussian t (fun h ↦ physical_floor floor h t)

/-- An unconditional physical comparison for the third event on the first 21 draws. -/
theorem horizontalCase_first21 (t : Fin 406) (ht : t.val ≤ 20) :
    probability (horizontalCase t.val) ≤ ballCharge 505 planeRadius
      (terminalLogFloor t.val-log winnerRadius) :=
  horizontalCase_gaussian t (fun h ↦ retained_floor_first20 h _ ht)

theorem prefix_bound_of_coverage (cover : LastCoordinateCoverage) :
    probability Prefix < 5.284/(10:ℝ)^15 :=
  prefix_numeric (concrete_prefix cover) FlagEnvelope.flagCharge_sum

theorem good_bound_of_coverage_floor (cover : LastCoordinateCoverage) (floor : LaterDeterminantFloor) :
    probability (fun A ↦ Good A ∧ terminalHit A) <
      probability residual₁ + probability residual₂ + 2.184/(10:ℝ)^12 :=
  good_numeric (concrete_prefix cover) (concrete_late floor) FlagEnvelope.flagCharge_sum

theorem terminal_bound_of_coverage_floor (cover : LastCoordinateCoverage) (floor : LaterDeterminantFloor) :
    probability terminalHit < probability residual₁ + probability residual₂ + 6.515/(10:ℝ)^12 :=
  terminal_numeric (concrete_prefix cover) (concrete_late floor) FlagEnvelope.flagCharge_sum

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.coverage_of_flag_lifts
#print axioms SigabaNeo.Wall1.ControlledPlane.laterFloor_of_hermite
#print axioms SigabaNeo.Wall1.ControlledPlane.good_bound_of_coverage_floor
#print axioms SigabaNeo.Wall1.ControlledPlane.concrete_prefix
#print axioms SigabaNeo.Wall1.ControlledPlane.concrete_late
#print axioms SigabaNeo.Wall1.ControlledPlane.horizontalCase_first21
#print axioms SigabaNeo.Wall1.ControlledPlane.prefix_bound_of_coverage
#print axioms SigabaNeo.Wall1.ControlledPlane.terminal_bound_of_coverage_floor

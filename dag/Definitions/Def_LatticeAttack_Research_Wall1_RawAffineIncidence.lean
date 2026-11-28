import Definitions.Def_LatticeAttack_Research_Wall1_RawPrefixMean
import Definitions.Def_LatticeAttack_Research_Wall1_AffineFactorialMoments

set_option autoImplicit true

/-! The actual raw syndrome count is an affine-graph incidence count. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane TerminalProjection QaryMembership
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- Reduce both integer blocks to their affine-graph coordinates. -/
def rawAffinePoint {k : ℕ} (z : Candidate k) : AffineGraphMoments.Point 400 k 3329 :=
  (reduce 3329 z.1, reduce 3329 z.2)

/-- The independent label is the offset column, followed by the raw matrix prefix. -/
def augmentedRawDesign {k : ℕ} (hk : k ≤ 512) (A : Sample) (c : Column) :
    Design 400 (k+1) 3329 :=
  fun i ↦ Fin.cons (c i) (fun j ↦ A i (j.castLE hk))

theorem incident_rawAffinePoint_iff {k : ℕ} (hk : k ≤ 512)
    (A : Sample) (c : Column) (z : Candidate k) :
    AffineGraphMoments.incident (augmentedRawDesign hk A c) (rawAffinePoint z) ↔
      rawSyndrome hk A z = c := by
  rw [AffineGraphMoments.incident_iff, ← raw_equation_iff_syndrome]
  simp only [augmentedRawDesign, rawAffinePoint, reduce, Fin.cons_zero, Fin.cons_succ]
  apply forall_congr'
  intro i
  simp only [mul_comm (A i _)]
  exact eq_comm

/-- Equality of the actual finite counts, with no distributional assumptions. -/
theorem finiteHitCount_augmentedRawDesign {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (A : Sample) (c : Column) :
    AffineGraphMoments.finiteHitCount T rawAffinePoint (augmentedRawDesign hk A c) =
      rawCount hk T A c := by
  classical
  rw [rawCount_eq_fiber]
  unfold AffineGraphMoments.finiteHitCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro z _
  exact incident_rawAffinePoint_iff hk A c z

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.incident_rawAffinePoint_iff
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.finiteHitCount_augmentedRawDesign

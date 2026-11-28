import Definitions.Def_LatticeAttack_Research_Wall1_RawAffineIncidence
import Definitions.Def_LatticeAttack_Research_Wall1_AffineOffsetPacking
import Definitions.Def_LatticeAttack_Research_Wall1_AffineDesignAverages

set_option autoImplicit true

/-! Exact rank-weighted factorial moments under the actual matrix-and-label law. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane TerminalProjection QaryMembership FactorialMomentTransfer
open AffineGraphMoments DualExit OrderedFiberTuples
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

lemma prefix_offsetDesign {k : ℕ} (hk : k ≤ 512) (A : Sample) (c : Column) :
    designPrefix (show k+1 ≤ 513 by omega) (offsetDesignEquiv 400 512 3329 (A,c)) =
      augmentedRawDesign hk A c := by
  funext i j
  refine Fin.cases ?_ (fun j ↦ ?_) j <;> rfl

/-- The raw joint law is exactly the uniform affine prefix law, without any gate. -/
theorem raw_factorial_average_affine {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (h : ℕ) :
    factorialAverage (rawCount hk T) h =
      average (fun B : Design 400 (k+1) 3329 ↦
        ((finiteHitCount T rawAffinePoint B).descFactorial h : ℝ)) := by
  let f (B : Design 400 (k+1) 3329) : ℝ :=
    ((finiteHitCount T rawAffinePoint B).descFactorial h : ℝ)
  have hp := average_offsetDesign (m := 400) (n := 512) (q := 3329)
    (fun B ↦ f (designPrefix (show k+1 ≤ 513 by omega) B))
  simp only [prefix_offsetDesign hk, f, finiteHitCount_augmentedRawDesign] at hp
  exact hp.trans (prefix_average (show k+1 ≤ 513 by omega) f)

/-- Every factorial order is an exact finite rank/consistency sum for the actual fixed family.
No centeredness or independence among candidates is assumed. -/
theorem raw_factorial_rank_sum {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (h : ℕ) :
    factorialAverage (rawCount hk T) h =
      ∑ e : orderedTuples T h, rankWeight (fun i ↦ rawAffinePoint (e i).val) := by
  rw [raw_factorial_average_affine]
  exact factorial_moment T rawAffinePoint h

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_factorial_average_affine
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_factorial_rank_sum

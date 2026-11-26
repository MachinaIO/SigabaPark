import Definitions.Def_LatticeAttack_Research_Wall1_RawPrefixOccupancy
import Mathlib.Data.ZMod.ValMinAbs

set_option autoImplicit true

/-! # The centered integer ball for the common-prefix certificate

This fixes the actual candidate set, 119 input columns, entries 15 through 404,
and the inclusive void threshold 7/25. Its remaining probabilistic input is the
raw empty-count sum; this file does not assert the Python numerical certificate.
-/

noncomputable section
namespace SigabaNeo.Wall1.CenteredPrefixOccupancy
open Finset ControlledPlane TerminalProjection RawPrefixOccupancy CosetOccupancy
open scoped Classical

def center {k : ℕ} (c : Column × (Fin k → ZMod 3329)) : Candidate k :=
  (fun i ↦ (c.1 i).valMinAbs, fun i ↦ (c.2 i).valMinAbs)

private theorem center_cast (x : ℤ) (h : -1664 ≤ x ∧ x ≤ 1664) :
    (x : ZMod 3329).valMinAbs = x := by
  apply (ZMod.valMinAbs_spec _ _).mpr
  refine ⟨rfl, ?_⟩
  change -(3329 : ℤ) < x * 2 ∧ x * 2 ≤ 3329
  omega

private def ballSet (k : ℕ) (r : ℝ) : Set (Candidate k) :=
  {z | (∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664) ∧
       (∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664) ∧ sqLength z.1 + sqLength z.2 ≤ r^2}

private theorem ballSet_finite (k : ℕ) (r : ℝ) : (ballSet k r).Finite := by
  apply (Set.finite_range (center (k := k))).subset
  intro z hz
  obtain ⟨ho, hv, _⟩ := hz
  refine ⟨((fun i ↦ (z.1 i : ZMod 3329)), (fun i ↦ (z.2 i : ZMod 3329))), ?_⟩
  apply Prod.ext <;> funext i
  · exact center_cast (z.1 i) (ho i)
  · exact center_cast (z.2 i) (hv i)

/-- The complete closed integer ball inside the centered residue cube. -/
def centeredBall (k : ℕ) (r : ℝ) : Finset (Candidate k) := (ballSet_finite k r).toFinset

/-- Membership is exactly the coordinate-centered closed ball, not a smaller subfamily. -/
theorem mem_centeredBall {k : ℕ} (r : ℝ) (z : Candidate k) :
    z ∈ centeredBall k r ↔
      (∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664) ∧
      (∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664) ∧
      sqLength z.1 + sqLength z.2 ≤ r^2 := by
  exact (ballSet_finite k r).mem_toFinset

/-- The squared length is an integer, even though the geometric API uses reals. -/
theorem sqLength_pair_integer {k : ℕ} (z : Candidate k) :
    ∃ n : ℤ, sqLength z.1 + sqLength z.2 = (n : ℝ) := by
  refine ⟨(∑ i, z.1 i ^ 2) + ∑ i, z.2 i ^ 2, ?_⟩
  simp [sqLength]

/-- Exact discretization: no integer candidate changes between consecutive squared radii. -/
theorem centeredBall_eq_sqrt_cutoff {k : ℕ} (r : ℝ) (n : ℕ)
    (hlo : (n : ℝ) ≤ r ^ 2) (hhi : r ^ 2 < (n : ℝ) + 1) :
    centeredBall k r = centeredBall k (Real.sqrt n) := by
  ext z
  rw [mem_centeredBall, mem_centeredBall, Real.sq_sqrt (Nat.cast_nonneg n)]
  obtain ⟨m, hm⟩ := sqLength_pair_integer z
  rw [hm]
  have hcut : (m : ℝ) ≤ r ^ 2 ↔ (m : ℝ) ≤ (n : ℝ) := by
    constructor
    · intro h
      have hlt : (m : ℝ) < (n : ℝ) + 1 := lt_of_le_of_lt h hhi
      have hint : m < (n : ℤ) + 1 := by exact_mod_cast hlt
      have hle : m ≤ (n : ℤ) := by omega
      exact_mod_cast hle
    · exact fun h ↦ le_trans h hlo
  rw [hcut]

/-- Exact radius of the integer candidate set identified by the interval certificate. -/
def slackRadius : ℝ := Real.sqrt 8415829

theorem slackBall_eq {k : ℕ} (r : ℝ)
    (hlo : (8415829 : ℝ) ≤ r ^ 2) (hhi : r ^ 2 < 8415830) :
    centeredBall k r = centeredBall k slackRadius := by
  apply centeredBall_eq_sqrt_cutoff r 8415829 hlo
  norm_num at *
  exact hhi

/-- Retained index14 corresponds to incoming draw15; index403 corresponds to draw404. -/
def entry (i : Fin 390) : ℕ := 14+i.val

-- Match the generic history theorem's classical existential decision procedure.
local instance (priority := 10000) historyExistsDecidable (p : Fin 390 → Prop) : Decidable (∃ i, p i) :=
  Classical.propDecidable _

/-- The concrete 119-input centered ball controls all eligible draws15..404 at threshold.280.
The right side is the sole raw first-moment quantity, with no factor390. -/
theorem centered_history_exit_first_moment (r : ℝ) (hr : 0 ≤ r)
    (radius : Fin 390 → Sample → ℝ) :
    7 * Fintype.card Column *
      (univ.filter fun A ↦ ∃ i, r ≤ radius i A ∧
        7 * Fintype.card (StateMark A (entry i)) ≤
          25 * emptyCount (occupied A (entry i) (radius i A))).card ≤
    25 * ∑ A, emptyCount (rawCount (by decide : 119 ≤ 512) (centeredBall 119 r) A) := by
  have result := actual_history_exit_first_moment (by decide : 119 ≤ 512)
    (centeredBall 119 r) entry
    (fun i ↦ by dsimp [entry]; omega)
    (fun i ↦ by dsimp [entry]; omega) hr
    (fun z hz ↦ ((mem_centeredBall r z).mp hz).2.2) radius 7 25
  exact result

/-- The exact integer slack ball controls every high-radius exit in the fixed horizon.
The numerical bound on the right-hand side remains a separate obligation. -/
theorem slack_history_exit_first_moment (radius : Fin 390 → Sample → ℝ) :
    7 * Fintype.card Column *
      (univ.filter fun A ↦ ∃ i, slackRadius ≤ radius i A ∧
        7 * Fintype.card (StateMark A (entry i)) ≤
          25 * emptyCount (occupied A (entry i) (radius i A))).card ≤
    25 * ∑ A, emptyCount
      (rawCount (by decide : 119 ≤ 512) (centeredBall 119 slackRadius) A) := by
  exact centered_history_exit_first_moment slackRadius (Real.sqrt_nonneg _) radius

end SigabaNeo.Wall1.CenteredPrefixOccupancy

#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.mem_centeredBall
#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.centered_history_exit_first_moment
#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.centeredBall_eq_sqrt_cutoff
#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.slackBall_eq
#print axioms SigabaNeo.Wall1.CenteredPrefixOccupancy.slack_history_exit_first_moment

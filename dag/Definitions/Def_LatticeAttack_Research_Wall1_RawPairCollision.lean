import Definitions.Def_LatticeAttack_Research_Wall1_RawPrefixMean

set_option autoImplicit true

/-! Exact collision probabilities for fixed centered raw candidate pairs. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane QaryMembership DualExit
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

lemma centered_intCast_injective {a b : ℤ}
    (ha : -1664 ≤ a ∧ a ≤ 1664) (hb : -1664 ≤ b ∧ b ≤ 1664)
    (he : (a : ZMod 3329) = (b : ZMod 3329)) : a = b := by
  have center (x : ℤ) (hx : -1664 ≤ x ∧ x ≤ 1664) :
      (x : ZMod 3329).valMinAbs = x := by
    apply (ZMod.valMinAbs_spec _ _).mpr
    refine ⟨rfl, ?_⟩
    change -(3329 : ℤ) < x * 2 ∧ x * 2 ≤ 3329
    omega
  have hh := congrArg ZMod.valMinAbs he
  simpa only [center a ha, center b hb] using hh

lemma rawSyndrome_collision_iff_kernel {k : ℕ} (hk : k ≤ 512)
    (A : Sample) (z w : Candidate k) :
    rawSyndrome hk A z = rawSyndrome hk A w ↔
      QaryMembership.kernel (designPrefix hk A) (w.1-z.1,z.2-w.2) := by
  simp only [rawSyndrome, QaryMembership.kernel, reduce, funext_iff,
    Matrix.mulVec, dotProduct, Pi.sub_apply, Int.cast_sub, Pi.neg_apply,
    designPrefix, mul_sub, sum_sub_distrib]
  apply forall_congr'
  intro i
  simp_rw [mul_comm (A i _) ]
  ring_nf
  constructor <;> intro h <;> linear_combination -h

lemma input_difference_ne_zero {k : ℕ} (z w : Candidate k)
    (hz : ∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664)
    (hw : ∀ i, -1664 ≤ w.2 i ∧ w.2 i ≤ 1664) (hne : z.2 ≠ w.2) :
    reduce 3329 (z.2-w.2) ≠ 0 := by
  intro he
  apply hne
  funext i
  apply centered_intCast_injective (hz i) (hw i)
  have hi := congrFun he i
  change ((z.2 i - w.2 i : ℤ) : ZMod 3329) = 0 at hi
  exact sub_eq_zero.mp (by simpa only [Int.cast_sub] using hi)

/-- Distinct centered input blocks impose one nonzero linear equation on every row. -/
theorem rawSyndrome_collision_probability_aux {k : ℕ} (hk : k ≤ 512)
    (z w : Candidate k)
    (hz : ∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664)
    (hw : ∀ i, -1664 ≤ w.2 i ∧ w.2 i ≤ 1664) (hne : z.2 ≠ w.2) :
    probability (fun A : Sample ↦ rawSyndrome hk A z = rawSyndrome hk A w) =
      1 / (3329 : ℝ)^400 := by
  simp_rw [rawSyndrome_collision_iff_kernel]
  rw [prefix_probability (m := 400) (q := 3329) hk
    (fun A : Design 400 k 3329 ↦ QaryMembership.kernel A (w.1-z.1,z.2-w.2))]
  have hh := kernel_fixed (q := 3329) (w.1-z.1,z.2-w.2)
    (input_difference_ne_zero z w hz hw hne)
  rw [card_univ] at hh
  have hreal : ((designs (fun A : Design 400 k 3329 ↦
      QaryMembership.kernel A (w.1-z.1,z.2-w.2))).card : ℝ) * (3329 : ℝ)^400 =
      Fintype.card (Design 400 k 3329) := by exact_mod_cast hh
  unfold probability
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (pow_ne_zero _ (by norm_num : (3329 : ℝ) ≠ 0))).mpr
  simpa only [one_mul] using hreal

theorem rawSyndrome_collision_probability {k : ℕ} (hk : k ≤ 512)
    (z w : Candidate k)
    (hz : ∀ i, -1664 ≤ z.2 i ∧ z.2 i ≤ 1664)
    (hw : ∀ i, -1664 ≤ w.2 i ∧ w.2 i ≤ 1664) (hne : z.2 ≠ w.2) :
    ((univ.filter fun A : Sample ↦ rawSyndrome hk A z = rawSyndrome hk A w).card : ℝ) /
      Fintype.card Sample = 1 / (3329 : ℝ)^400 := by
  have h := rawSyndrome_collision_probability_aux hk z w hz hw hne
  have he : designs (fun A : Sample ↦ rawSyndrome hk A z = rawSyndrome hk A w) =
      univ.filter (fun A : Sample ↦ rawSyndrome hk A z = rawSyndrome hk A w) := by
    ext A
    simp only [designs, mem_filter]
  unfold probability at h
  rw [he] at h
  exact h

/-- With the same input, distinct centered outputs can never have the same raw label. -/
theorem rawSyndrome_ne_of_same_input {k : ℕ} (hk : k ≤ 512)
    (A : Sample) (z w : Candidate k)
    (hz : ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664)
    (hw : ∀ i, -1664 ≤ w.1 i ∧ w.1 i ≤ 1664)
    (hin : z.2 = w.2) (hout : z.1 ≠ w.1) :
    rawSyndrome hk A z ≠ rawSyndrome hk A w := by
  intro he
  apply hout
  funext i
  apply centered_intCast_injective (hz i) (hw i)
  have hi := congrFun he i
  dsimp [rawSyndrome] at hi
  rw [hin] at hi
  exact sub_left_inj.mp hi

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.rawSyndrome_collision_probability
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.rawSyndrome_ne_of_same_input

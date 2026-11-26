module

public import Definitions.Def_LatticeAttack_Attacks_Primal_SampleDeletionCBD
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1.CBDTail

open SampleDeletion
open scoped BigOperators

noncomputable def weight (j : Digit 3) : ℝ := (mass j : ℝ) / 64

noncomputable def jointWeight {d : ℕ} (x : Fin d → Digit 3) : ℝ := ∏ i, weight (x i)

noncomputable def projection {d : ℕ} (a : Fin d → ℝ) (x : Fin d → Digit 3) : ℝ :=
  ∑ i, a i * (centered (x i) : ℝ)

theorem cosh_six_le (s : ℝ) : Real.cosh (s / 2) ^ 6 ≤ Real.exp (3 * s ^ 2 / 4) := by
  calc
    _ ≤ Real.exp ((s / 2) ^ 2 / 2) ^ 6 :=
      pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem coordinate_mgf (s : ℝ) :
    ∑ j : Digit 3, weight j * Real.exp (s * (centered j : ℝ)) = Real.cosh (s / 2) ^ 6 := by
  have term (j : Digit 3) : Real.exp (s * (centered j : ℝ)) =
      Real.exp s ^ j.val * Real.exp (-(3 * s)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    simp [centered]
    ring
  have hc : Real.cosh (s / 2) = (Real.exp s + 1) * Real.exp (-(s / 2)) / 2 := by
    rw [Real.cosh_eq, add_mul, ← Real.exp_add, one_mul, show s + -(s / 2) = s / 2 by ring]
  simp_rw [term]
  rw [hc, div_pow, mul_pow, ← Real.exp_nat_mul,
    show ((6 : ℕ) : ℝ) * -(s / 2) = -(3 * s) by push_cast; ring]
  change (∑ j : Fin 7, _) = _
  norm_num [Fin.sum_univ_succ, weight, mass, Nat.choose]; ring

theorem product_mgf_le {d : ℕ} (a : Fin d → ℝ) (s : ℝ) :
    ∑ x, jointWeight x * Real.exp (s * projection a x) ≤
      Real.exp (3 * s ^ 2 / 4 * ∑ i, a i ^ 2) := by
  classical
  let f (i : Fin d) (j : Digit 3) := weight j * Real.exp ((s * a i) * (centered j : ℝ))
  calc
    _ = ∑ x : Fin d → Digit 3, ∏ i, f i (x i) := by
      simp only [f, projection, jointWeight, Finset.mul_sum, Real.exp_sum,
        Finset.prod_mul_distrib, mul_assoc]
    _ = ∏ i, ∑ j, f i j := (Fintype.prod_sum f).symm
    _ = ∏ i, Real.cosh (s * a i / 2) ^ 6 := by simp only [f, coordinate_mgf]
    _ ≤ ∏ i, Real.exp (3 * (s * a i) ^ 2 / 4) :=
      Finset.prod_le_prod₀ (fun i _ ↦ by positivity) (fun i _ ↦ cosh_six_le _)
    _ = _ := by
      rw [← Real.exp_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intros
      ring

private theorem markov {d : ℕ} (a : Fin d → ℝ) (t s : ℝ) (hs : s ≤ 0) :
    ∑ x : Fin d → Digit 3 with projection a x ≤ -t, jointWeight x ≤
      Real.exp (s * t + 3 * s ^ 2 / 4 * ∑ i, a i ^ 2) := by
  classical
  have hw (x : Fin d → Digit 3) : 0 ≤ jointWeight x := by
    unfold jointWeight weight
    positivity
  rw [Real.exp_add, mul_comm (Real.exp (s * t))]
  calc
    _ ≤ ∑ x : Fin d → Digit 3, (jointWeight x * Real.exp (s * projection a x)) *
        Real.exp (s * t) := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro x _
      split_ifs with hx
      · rw [mul_assoc, ← Real.exp_add]
        exact le_mul_of_one_le_right (hw x) (Real.one_le_exp_iff.mpr (by nlinarith [mul_nonneg (neg_nonneg.mpr hs) (show 0 ≤ -t - projection a x by linarith)]))
      · exact mul_nonneg (mul_nonneg (hw x) (Real.exp_pos _).le) (Real.exp_pos _).le
    _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (product_mgf_le a s) (Real.exp_pos _).le

theorem lower_tail {d : ℕ} (a : Fin d → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    ∑ x : Fin d → Digit 3 with projection a x ≤ -t, jointWeight x ≤
      Real.exp (-t ^ 2 / (3 * ∑ i, a i ^ 2)) := by
  let q := ∑ i, a i ^ 2
  have hq : 0 ≤ q := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  let s := -(2 * t) / (3 * q)
  have hs : s ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  apply (markov a t s hs).trans_eq
  congr 1
  change s * t + 3 * s ^ 2 / 4 * q = -t ^ 2 / (3 * q)
  by_cases hz : q = 0
  · simp [s, hz]
  · dsimp [s]; field_simp; ring

theorem half_energy_tail {d : ℕ} (h : Fin d → ℝ) :
    ∑ x : Fin d → Digit 3 with projection h x ≤ -((∑ i, h i ^ 2) / 2), jointWeight x ≤
      Real.exp (-(∑ i, h i ^ 2) / 12) := by
  apply (markov h _ (-(1/3)) (by norm_num)).trans_eq
  congr 1
  ring

#print axioms cosh_six_le
#print axioms coordinate_mgf
#print axioms product_mgf_le
#print axioms lower_tail
#print axioms half_energy_tail

end SigabaNeo.Wall1.CBDTail

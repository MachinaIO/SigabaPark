import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ℝ) (c : ι → ZMod 2) :
    ∑ x : ι → ZMod 2, (∏ i, (if x i = 1 then τ else 1 - τ)) * (-1 : ℝ) ^ (∑ i, c i * x i).val
      = ∏ i, (if c i = 0 then (1 : ℝ) else 1 - 2 * τ) := by
  have hadd : ∀ a b : ZMod 2, (-1 : ℝ) ^ (a + b).val = (-1 : ℝ) ^ a.val * (-1 : ℝ) ^ b.val := by
    have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    intro a b
    rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;>
      simp [show ((1 : ZMod 2) + 1) = 0 from rfl, ZMod.val_one]
  have hsum : ∀ (s : Finset ι) (f : ι → ZMod 2),
      (-1 : ℝ) ^ (∑ i ∈ s, f i).val = ∏ i ∈ s, (-1 : ℝ) ^ (f i).val := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]
  have key : ∀ x : ι → ZMod 2,
      (∏ i, (if x i = 1 then τ else 1 - τ)) * (-1 : ℝ) ^ (∑ i, c i * x i).val
        = ∏ i, ((if x i = 1 then τ else 1 - τ) * (-1 : ℝ) ^ (c i * x i).val) := by
    intro x; rw [hsum, Finset.prod_mul_distrib]
  simp_rw [key]
  rw [← Fintype.prod_sum (fun i (z : ZMod 2) => (if z = 1 then τ else 1 - τ) * (-1 : ℝ) ^ (c i * z).val)]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide, Finset.sum_pair (by decide)]
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h01 (c i) with h | h <;> rw [h]
  · simp
  · simp [ZMod.val_one]; ring

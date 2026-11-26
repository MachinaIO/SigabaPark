module

public import Mathlib

set_option autoImplicit true

/-! # First-vector bound from block Hermite inequalities

The prefix sums of log GSO lengths obey a discrete maximum principle. With block size
β and uniform log-norm allowance c, the first log length exceeds the mean by at most
c ((n-1)/(β-1)+1). This is a fully reduced profile bound. Hanrot, Pujol and Stehlé
(CRYPTO 2011) also analyze the dynamics of finite tours; we do not model tours.
-/

public section

namespace SigabaNeo.BKZ

/-- Log determinant of the first i Gram–Schmidt vectors when their log lengths are r. -/
@[expose] def logPrefix (r : ℕ → ℝ) (i : ℕ) := ∑ j ∈ Finset.range i, r j

/-- The difference of prefix sums is the log determinant of the block. -/
@[expose] def BlockProfile (r : ℕ → ℝ) (n β : ℕ) (c : ℝ) : Prop :=
  ∀ i < n, let k := min β (n-i)
           (k : ℝ) * r i ≤ k*c + logPrefix r (i+k) - logPrefix r i

theorem first_log_bound {r : ℕ → ℝ} {n β : ℕ} {c : ℝ} (hb : 2 ≤ β)
    (hn : β ≤ n) (hc : 0 ≤ c) (h : BlockProfile r n β c) :
    r 0 - logPrefix r n / n ≤ c / (β-1) * (n-1) + c := by
  classical
  let a := c / ((β : ℝ)-1)
  let m := logPrefix r n / n
  let B := fun (x : ℝ) ↦ x*(m+c) + a*x*(n-x)
  let q := fun (i : ℕ) ↦ logPrefix r i - B i
  have nb : (1 : ℝ) < β := by exact_mod_cast (show 1 < β by omega)
  have np : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 ≤ a := div_nonneg hc (by linarith)
  have hab : a*((β : ℝ)-1) = c := div_mul_cancel₀ _ (by linarith)
  have hzero : q 0 = 0 := by simp [q, B, logPrefix]
  have hend : q n = -(n*c) := by
    dsimp [q,B,m]
    field_simp
    ring
  suffices hs : q 1 ≤ 0 by
    have hs' : r 0 - ((m+c)+a*(n-1)) ≤ 0 := by simpa [q,B,logPrefix] using hs
    change r 0 - m ≤ a*(n-1)+c
    linarith
  by_contra! hp
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image (Finset.range (n+1)) q
    ⟨0, by simp⟩
  have ex : ∃ j, j ≤ n ∧ q j = q t := ⟨t, by simpa using ht, rfl⟩
  let j := Nat.find ex
  obtain ⟨hjn,hjt⟩ := Nat.find_spec ex
  change j ≤ n at hjn
  change q j = q t at hjt
  have hjpos : 0 < q j := hp.trans_le (hjt ▸ hmax 1 (Finset.mem_range.mpr (by omega)))
  have hneq : j ≠ n := fun e ↦ by rw [e,hend] at hjpos; nlinarith
  have hj0 : j ≠ 0 := fun e ↦ by rw [e,hzero] at hjpos; linarith
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  let k := min β (n-i)
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hik : i+k ≤ n := by dsimp [k]; omega
  have hprev : q i < q j := by
    apply lt_of_le_of_ne
    · rw [hjt]; exact hmax i (Finset.mem_range.mpr (by omega))
    · intro e
      have := Nat.find_min ex (show i < j by omega)
      exact this ⟨by omega,e.trans hjt⟩
  have hnext : q (i+k) ≤ q j := by
    rw [hjt]; exact hmax _ (Finset.mem_range.mpr (by omega))
  have bl := h i (by omega)
  change (k:ℝ)*r i ≤ k*c + logPrefix r (i+k) - logPrefix r i at bl
  have step : logPrefix r (i+1) = logPrefix r i + r i := Finset.sum_range_succ _ _
  have recurrence : (k:ℝ)*q j ≤ (k-1)*q i + q (i+k) + k*(c-a*(k-1)) := by
    rw [hi]
    simp only [q,B,Nat.cast_add,Nat.cast_succ,step]
    nlinarith
  have hk' : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have prev := mul_lt_mul_of_pos_left hprev (sub_pos.mpr hk')
  by_cases e : k = β
  · rw [e,hab] at recurrence
    rw [e] at prev
    rw [e] at hnext
    linarith
  · have endeq : i+k = n := by dsimp [k] at *; omega
    rw [endeq,hend] at recurrence
    have kn : (k:ℝ) ≤ n := by exact_mod_cast (show k ≤ n by omega)
    nlinarith [mul_le_mul_of_nonneg_right kn hc,
      mul_nonneg (show 0 ≤ (k:ℝ) by positivity) (mul_nonneg ha (sub_nonneg.mpr hk'.le))]

end SigabaNeo.BKZ

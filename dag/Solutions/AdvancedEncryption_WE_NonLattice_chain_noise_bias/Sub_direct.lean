import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

theorem solution {L m n : ℕ} (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1 / 2) (ρ : ℕ)
    (r : Fin L → Fin m → ZMod 2) (h : Fin L → Fin n → ZMod 2)
    (hr : ∀ i, r i ≠ 0) (hh : ∀ i, ρ ≤ (Finset.univ.filter fun b => h i b ≠ 0).card) :
    ∑ E : Fin L × Fin m × Fin n → ZMod 2,
        (∏ t, (if E t = 1 then τ else 1 - τ)) *
          (-1 : ℝ) ^ (∑ t, r t.1 t.2.1 * E t * h t.1 t.2.2).val
      = (1 - 2 * τ) ^ (∑ i, (Finset.univ.filter fun a => r i a ≠ 0).card *
          (Finset.univ.filter fun b => h i b ≠ 0).card) ∧
    (1 - 2 * τ) ^ (∑ i, (Finset.univ.filter fun a => r i a ≠ 0).card *
          (Finset.univ.filter fun b => h i b ≠ 0).card) ≤ (1 - 2 * τ) ^ (L * ρ) := by
  -- the general piling-up identity for one parity of independent biased bits
  have pile : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ZMod 2),
      ∑ x : ι → ZMod 2, (∏ i, (if x i = 1 then τ else 1 - τ)) * (-1 : ℝ) ^ (∑ i, c i * x i).val
        = ∏ i, (if c i = 0 then (1 : ℝ) else 1 - 2 * τ) := by
    intro ι _ _ c
    have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    have hadd : ∀ a b : ZMod 2, (-1 : ℝ) ^ (a + b).val = (-1 : ℝ) ^ a.val * (-1 : ℝ) ^ b.val := by
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
    rw [← Fintype.prod_sum
      (fun i (z : ZMod 2) => (if z = 1 then τ else 1 - τ) * (-1 : ℝ) ^ (c i * z).val)]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide, Finset.sum_pair (by decide)]
    rcases h01 (c i) with hc | hc <;> rw [hc]
    · simp
    · simp [ZMod.val_one]; ring
  set wr : Fin L → ℕ := fun i => (Finset.univ.filter fun a => r i a ≠ 0).card
  set wh : Fin L → ℕ := fun i => (Finset.univ.filter fun b => h i b ≠ 0).card
  refine ⟨?_, ?_⟩
  · have hc : ∀ E : Fin L × Fin m × Fin n → ZMod 2,
        (∑ t, r t.1 t.2.1 * E t * h t.1 t.2.2) = ∑ t, (r t.1 t.2.1 * h t.1 t.2.2) * E t := by
      intro E; refine Finset.sum_congr rfl (fun t _ => ?_); ring
    simp_rw [hc]
    rw [pile (fun t : Fin L × Fin m × Fin n => r t.1 t.2.1 * h t.1 t.2.2)]
    have hpow : ∀ t : Fin L × Fin m × Fin n,
        (if r t.1 t.2.1 * h t.1 t.2.2 = 0 then (1 : ℝ) else 1 - 2 * τ)
          = (1 - 2 * τ) ^ ((if r t.1 t.2.1 ≠ 0 then 1 else 0) * (if h t.1 t.2.2 ≠ 0 then 1 else 0)) := by
      intro t
      have hmz : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by decide
      by_cases h1 : r t.1 t.2.1 = 0
      · simp [h1]
      by_cases h2 : h t.1 t.2.2 = 0
      · simp [h2]
      simp [h1, h2, hmz _ _ h1 h2]
    simp_rw [hpow]
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fintype.sum_prod_type]
    simp only [Finset.card_filter]
    rw [Finset.sum_mul_sum]
  · have hb0 : 0 ≤ 1 - 2 * τ := by linarith
    have hb1 : 1 - 2 * τ ≤ 1 := by linarith
    apply pow_le_pow_of_le_one hb0 hb1
    have : ∀ i, ρ ≤ wr i * wh i := by
      intro i
      have h1 : 1 ≤ wr i := by
        obtain ⟨a, ha⟩ : ∃ a, r i a ≠ 0 := by
          by_contra hne; exact hr i (funext fun a => by by_contra hx; exact hne ⟨a, hx⟩)
        exact Finset.card_pos.mpr ⟨a, by simp [ha]⟩
      calc ρ ≤ wh i := hh i
        _ = 1 * wh i := (one_mul _).symm
        _ ≤ wr i * wh i := Nat.mul_le_mul_right _ h1
    calc L * ρ = ∑ _i : Fin L, ρ := by simp
      _ ≤ ∑ i, wr i * wh i := Finset.sum_le_sum (fun i _ => this i)

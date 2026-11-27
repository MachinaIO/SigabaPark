module

public import Definitions.Def_LatticeAttack_Research_Wall1_CBDQuadratic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Algebra.Order.Round
import all Definitions.Def_LatticeAttack_Research_Wall1_CBDTail
import Mathlib.Tactic

set_option autoImplicit true

/-! # The Babai lift of Part 47 (PROOF_GAP Wall 1)

Part 47 (`docs/research/wall1_decoupled.md`, audit note) lifts the SVP output of the decoupled
attack `L = L₀ ⊕ ℤu` back through the prefix `K = span_ℤ(b₀, …, b_{j-1})` by Babai's
nearest-plane algorithm. The audited claim is

* (deterministic) Babai on the prefix, applied to any lift `u + k` (`k ∈ K`), returns `u` exactly
  when `|⟨u, b*ᵢ⟩| < ‖b*ᵢ‖²/2` for every prefix index `i`;
* (probabilistic) for the CBD(η) plant, `Pr[lift fails] ≤ Σᵢ 2 exp(−gᵢ²/(4η))`.

This file proves both, for CBD(3) (`η = 3`, so `4η = 12`).

Setting. `b bs : ℕ → E` in a real inner product space; the prefix is the indices `< n`. The only
property of `bs` used is the Gram–Schmidt triangularity `IsGSPair`:
`⟨b l, bs m⟩ = 0` for `l < m` and `⟨b m, bs m⟩ = ‖bs m‖²`. `gramSchmidt_isGSPair` shows that
Mathlib's `gramSchmidt ℝ b` satisfies it; no linear independence is needed.

Main results.
* `babai`: nearest-plane, processing the indices `n-1, …, 0`.
* `babai_sub_mem`, `babai_box`: the output differs from the target by an integer prefix
  combination and lies in the closed box `|⟨·, bs i⟩| ≤ ‖bs i‖²/2`.
* `box_unique`: the closed box meets each coset `u + K` only at `u` when `u` is in the open box.
* `babai_lift` (**deterministic lemma**): if `|⟨u, bs i⟩| < ‖bs i‖²/2` for all `i < n`, then
  `babai n (u + Σ cᵢ bᵢ) = u` for every integer vector `c`.
* `tail_two_sided`: for CBD(3) `x` and `Σ aᵢ² ≤ T`, `Pr[|Σ aᵢ xᵢ| ≥ T/2] ≤ 2 exp(−T/12)`.
* `liftFail_le` (**probabilistic lemma**): if `⟨U x, bs i⟩ = Σ_c a i c · x_c` (centered CBD(3)
  coordinates) with `Σ_c (a i c)² ≤ ‖bs i‖²` for `i < n`, then the CBD(3) mass of plants for which
  Babai fails on *some* lift is `≤ Σ_{i<n} 2 exp(−‖bs i‖²/12)`.
* `liftFail_le_floor`: the same with a prefix floor `gᵢ ≤ ‖bs i‖`, giving
  `ℓ = Σ_{i<n} 2 exp(−gᵢ²/12)`, i.e. exactly the documented `Σ 2 exp(−gᵢ²/(4η))` at `η = 3`. -/

public section

namespace SigabaNeo.Wall1.BabaiLift

open SampleDeletion CBDTail InnerProductSpace Classical
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Gram–Schmidt triangularity -/

/-- `bs` is a Gram–Schmidt system for `b`: `b l ⟂ bs m` for `l < m`, and `⟨b m, bs m⟩ = ‖bs m‖²`. -/
structure IsGSPair (b bs : ℕ → E) : Prop where
  upper : ∀ l m, l < m → inner ℝ (b l) (bs m) = 0
  diag : ∀ m, inner ℝ (b m) (bs m) = ‖bs m‖ ^ 2

/-- Mathlib's Gram–Schmidt process is a Gram–Schmidt system. -/
theorem gramSchmidt_isGSPair (b : ℕ → E) : IsGSPair b (gramSchmidt ℝ b) where
  upper l m h := by
    rw [real_inner_comm]
    exact gramSchmidt_inv_triangular ℝ b h
  diag m := by
    nth_rewrite 1 [gramSchmidt_def'' ℝ b m]
    rw [inner_add_left, sum_inner, real_inner_self_eq_norm_sq, Finset.sum_eq_zero, add_zero]
    intro i hi
    rw [real_inner_smul_left, gramSchmidt_orthogonal ℝ b (Finset.mem_Iio.1 hi).ne, mul_zero]

/-! ## Integer prefix combinations and the algorithm -/

/-- The prefix lattice vector `Σ_{i<n} cᵢ bᵢ`. -/
noncomputable def comb (b : ℕ → E) (c : ℕ → ℤ) (n : ℕ) : E :=
  ∑ i ∈ Finset.range n, (c i : ℝ) • b i

theorem comb_sub (b : ℕ → E) (c c' : ℕ → ℤ) (n : ℕ) :
    comb b c n - comb b c' n = comb b (c - c') n := by
  simp only [comb, ← Finset.sum_sub_distrib, Pi.sub_apply, Int.cast_sub, sub_smul]

theorem inner_comb_of_le {b bs : ℕ → E} (h : IsGSPair b bs) (c : ℕ → ℤ) {n m : ℕ}
    (hm : n ≤ m) : inner ℝ (comb b c n) (bs m) = 0 := by
  unfold comb
  rw [sum_inner]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [real_inner_smul_left, h.upper i m (by have := Finset.mem_range.1 hi; omega), mul_zero]

theorem inner_comb_succ {b bs : ℕ → E} (h : IsGSPair b bs) (c : ℕ → ℤ) (m : ℕ) :
    inner ℝ (comb b c (m + 1)) (bs m) = c m * ‖bs m‖ ^ 2 := by
  have := inner_comb_of_le h c (le_refl m)
  unfold comb at this ⊢
  rw [Finset.sum_range_succ, inner_add_left, this, real_inner_smul_left, h.diag, zero_add]

/-- **Babai's nearest-plane algorithm** on the prefix `b 0, …, b (n-1)` with Gram–Schmidt vectors
`bs`: subtract `round(⟨t, bs i⟩/‖bs i‖²) · b i` for `i = n-1, …, 0`. -/
noncomputable def babai (b bs : ℕ → E) : ℕ → E → E
  | 0, t => t
  | n + 1, t => babai b bs n (t - ((round (inner ℝ t (bs n) / ‖bs n‖ ^ 2) : ℤ) : ℝ) • b n)

/-- The Babai output is the target minus an integer prefix combination. -/
theorem babai_sub_mem (b bs : ℕ → E) (n : ℕ) (t : E) :
    ∃ c : ℕ → ℤ, babai b bs n t = t - comb b c n := by
  induction n generalizing t with
  | zero => exact ⟨0, by simp [babai, comb]⟩
  | succ n ih =>
    set r : ℤ := round (inner ℝ t (bs n) / ‖bs n‖ ^ 2)
    obtain ⟨c, hc⟩ := ih (t - (r : ℝ) • b n)
    refine ⟨Function.update c n r, ?_⟩
    have hs : comb b (Function.update c n r) n = comb b c n := by
      unfold comb
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [Function.update_of_ne (Finset.mem_range.1 hi).ne]
    change babai b bs n (t - (r : ℝ) • b n) = _
    have hsucc : comb b (Function.update c n r) (n + 1) = comb b c n + (r : ℝ) • b n := by
      rw [comb, Finset.sum_range_succ, ← comb, hs, Function.update_self]
    rw [hc, hsucc]
    abel

/-- The Babai output lies in the closed box `|⟨·, bs i⟩| ≤ ‖bs i‖²/2` for every prefix index. -/
theorem babai_box {b bs : ℕ → E} (h : IsGSPair b bs) (n : ℕ) (t : E) :
    ∀ i < n, |inner ℝ (babai b bs n t) (bs i)| ≤ ‖bs i‖ ^ 2 / 2 := by
  induction n generalizing t with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    set r : ℤ := round (inner ℝ t (bs n) / ‖bs n‖ ^ 2)
    change |inner ℝ (babai b bs n (t - (r : ℝ) • b n)) (bs i)| ≤ _
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih _ i hi
    obtain ⟨c, hc⟩ := babai_sub_mem b bs i (t - (r : ℝ) • b i)
    rw [hc, inner_sub_left, inner_comb_of_le h c le_rfl, sub_zero, inner_sub_left,
      real_inner_smul_left, h.diag]
    by_cases hz : bs i = 0
    · simp [hz]
    have hs : 0 < ‖bs i‖ ^ 2 := by positivity
    have hround := abs_sub_round (inner ℝ t (bs i) / ‖bs i‖ ^ 2)
    have key : inner ℝ t (bs i) - (r : ℝ) * ‖bs i‖ ^ 2 =
        (inner ℝ t (bs i) / ‖bs i‖ ^ 2 - r) * ‖bs i‖ ^ 2 := by
      field_simp
    rw [key, abs_mul, abs_of_pos hs]
    nlinarith

/-- **Uniqueness in the box.** If `y = u + Σ_{i<n} cᵢ bᵢ`, `y` lies in the closed box and `u` in
the open box, then `y = u`. -/
theorem box_unique {b bs : ℕ → E} (h : IsGSPair b bs) (n : ℕ) (u : E)
    (hu : ∀ i < n, |inner ℝ u (bs i)| < ‖bs i‖ ^ 2 / 2) (c : ℕ → ℤ) (y : E)
    (hy : ∀ i < n, |inner ℝ y (bs i)| ≤ ‖bs i‖ ^ 2 / 2) (hyu : y = u + comb b c n) : y = u := by
  induction n generalizing y with
  | zero => simpa [comb] using hyu
  | succ n ih =>
    have hin := congrArg (fun v ↦ inner ℝ v (bs n)) hyu
    simp only [inner_add_left, inner_comb_succ h] at hin
    have h1 := hy n (Nat.lt_succ_self n)
    have h2 := hu n (Nat.lt_succ_self n)
    have hs : 0 < ‖bs n‖ ^ 2 := by
      by_contra hs
      have : ‖bs n‖ ^ 2 = 0 := le_antisymm (not_lt.1 hs) (sq_nonneg _)
      rw [this] at h2
      linarith [abs_nonneg (inner ℝ u (bs n))]
    have hc : c n = 0 := by
      have hlt : |(c n : ℝ)| * ‖bs n‖ ^ 2 < 1 * ‖bs n‖ ^ 2 := by
        have : (c n : ℝ) * ‖bs n‖ ^ 2 = inner ℝ y (bs n) - inner ℝ u (bs n) := by linarith
        rw [← abs_of_pos hs, ← abs_mul, this, abs_of_pos hs]
        calc _ ≤ |inner ℝ y (bs n)| + |inner ℝ u (bs n)| := abs_sub _ _
          _ < _ := by linarith
      have := lt_of_mul_lt_mul_right hlt hs.le
      have : |c n| < 1 := by exact_mod_cast this
      have := abs_lt.1 this
      omega
    refine ih (fun i hi ↦ hu i (by omega)) y (fun i hi ↦ hy i (by omega)) ?_
    rw [hyu, comb, Finset.sum_range_succ, hc]
    simp [comb]

/-- **Deterministic Babai lift (Part 47).** If the target error `u` satisfies
`|⟨u, bs i⟩| < ‖bs i‖²/2` for every prefix index `i < n`, then Babai's nearest plane on the prefix
recovers `u` exactly from every lift `u + Σ_{i<n} cᵢ bᵢ`. -/
theorem babai_lift {b bs : ℕ → E} (h : IsGSPair b bs) (n : ℕ) (u : E)
    (hu : ∀ i < n, |inner ℝ u (bs i)| < ‖bs i‖ ^ 2 / 2) (c : ℕ → ℤ) :
    babai b bs n (u + comb b c n) = u := by
  obtain ⟨c', hc'⟩ := babai_sub_mem b bs n (u + comb b c n)
  refine box_unique h n u hu (c - c') _ (babai_box h n _) ?_
  rw [hc', ← comb_sub]
  abel

/-! ## The CBD(3) tail -/

private theorem weight_nonneg {d : ℕ} (x : Fin d → Digit 3) : 0 ≤ jointWeight x := by
  unfold jointWeight weight
  positivity

private theorem filter_mass_le_one {d : ℕ} (S : (Fin d → Digit 3) → Prop) [DecidablePred S] :
    ∑ x with S x, jointWeight x ≤ 1 := by
  rw [← CBDQuadratic.joint_mass (N := d)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun x _ _ ↦ weight_nonneg x

private theorem projection_neg {d : ℕ} (a : Fin d → ℝ) (x : Fin d → Digit 3) :
    projection (-a) x = -projection a x := by
  simp [projection, Finset.sum_neg_distrib]

private theorem one_sided {d : ℕ} (a : Fin d → ℝ) {T : ℝ} (hT : 0 < T)
    (ha : ∑ c, a c ^ 2 ≤ T) :
    ∑ x with projection a x ≤ -(T / 2), jointWeight x ≤ Real.exp (-T / 12) := by
  classical
  set S := ∑ c, a c ^ 2
  by_cases hS : S = 0
  · have h0 : ∀ c, a c = 0 := by
      intro c
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ ↦ sq_nonneg (a c))).1 hS c
        (Finset.mem_univ _)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have : (Finset.univ.filter fun x : Fin d → Digit 3 ↦ projection a x ≤ -(T / 2)) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun x _ hx ↦ ?_
      have hp : projection a x = 0 := by simp [projection, h0]
      rw [hp] at hx
      linarith
    rw [this, Finset.sum_empty]
    positivity
  have hSpos : 0 < S := lt_of_le_of_ne (Finset.sum_nonneg fun c _ ↦ sq_nonneg _) (Ne.symm hS)
  refine (lower_tail a (T / 2) (by linarith)).trans (Real.exp_le_exp.2 ?_)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **Two-sided CBD(3) tail.** If `Σ aᵢ² ≤ T` then `Pr[|Σ aᵢ xᵢ| ≥ T/2] ≤ 2 exp(−T/12)` for
`x` iid CBD(3) (centered). This is the sub-Gaussian bound with variance proxy `η/2 = 3/2`. -/
theorem tail_two_sided {d : ℕ} (a : Fin d → ℝ) {T : ℝ} (hT : 0 ≤ T) (ha : ∑ c, a c ^ 2 ≤ T) :
    ∑ x with T / 2 ≤ |projection a x|, jointWeight x ≤ 2 * Real.exp (-T / 12) := by
  classical
  rcases hT.eq_or_lt with rfl | hT
  · refine (filter_mass_le_one _).trans ?_
    simp
  have split : ∑ x with T / 2 ≤ |projection a x|, jointWeight x ≤
      ∑ x with projection a x ≤ -(T / 2), jointWeight x +
        ∑ x with projection (-a) x ≤ -(T / 2), jointWeight x := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    have hw := weight_nonneg x
    rw [projection_neg]
    by_cases h1 : projection a x ≤ -(T / 2) <;> by_cases h2 : -projection a x ≤ -(T / 2) <;>
      by_cases h3 : T / 2 ≤ |projection a x| <;> simp only [h1, h2, h3, ite_true, ite_false] <;>
      first | linarith | (exfalso; rw [le_abs] at h3; rcases h3 with h3 | h3 <;> linarith)
  have hneg : ∑ c, (-a) c ^ 2 ≤ T := by simpa using ha
  linarith [one_sided a hT ha, one_sided (-a) hT hneg]

/-! ## The probabilistic lift bound -/

/-- The lift fails for the plant vector `u`: Babai on the prefix of length `n` does not return `u`
from *some* lift `u + Σ cᵢ bᵢ`. -/
@[expose] def LiftFail (b bs : ℕ → E) (n : ℕ) (u : E) : Prop :=
  ∃ c : ℕ → ℤ, babai b bs n (u + comb b c n) ≠ u

theorem liftFail_imp {b bs : ℕ → E} (h : IsGSPair b bs) {n : ℕ} {u : E}
    (hf : LiftFail b bs n u) : ∃ i < n, ‖bs i‖ ^ 2 / 2 ≤ |inner ℝ u (bs i)| := by
  by_contra hne
  push Not at hne
  obtain ⟨c, hc⟩ := hf
  exact hc (babai_lift h n u hne c)

/-- **Probabilistic Babai lift (Part 47), CBD(3).** Let the plant vector be `U x` for
`x : Fin d → Digit 3` iid CBD(3), and suppose that on the prefix `⟨U x, bs i⟩ = Σ_c a i c · x_c`
(centered coordinates) with `Σ_c (a i c)² ≤ ‖bs i‖²` (e.g. `bs i` horizontal). Then the CBD(3)
probability that Babai fails on some lift is at most `Σ_{i<n} 2 exp(−‖bs i‖²/12)`. -/
theorem liftFail_le {b bs : ℕ → E} (h : IsGSPair b bs) (n : ℕ) {d : ℕ}
    (U : (Fin d → Digit 3) → E) (a : ℕ → Fin d → ℝ)
    (hU : ∀ x, ∀ i < n, inner ℝ (U x) (bs i) = projection (a i) x)
    (ha : ∀ i < n, ∑ c, a i c ^ 2 ≤ ‖bs i‖ ^ 2) :
    ∑ x with LiftFail b bs n (U x), jointWeight x ≤
      ∑ i ∈ Finset.range n, 2 * Real.exp (-‖bs i‖ ^ 2 / 12) := by
  classical
  calc _ ≤ ∑ i ∈ Finset.range n, ∑ x with ‖bs i‖ ^ 2 / 2 ≤ |projection (a i) x|,
        jointWeight x := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun x _ ↦ ?_
        split_ifs with hf
        · obtain ⟨i, hi, hb⟩ := liftFail_imp h hf
          rw [hU x i hi] at hb
          refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun i ↦
            if ‖bs i‖ ^ 2 / 2 ≤ |projection (a i) x| then jointWeight x else 0)
            (fun j _ ↦ by split_ifs <;> simp [weight_nonneg]) (Finset.mem_range.2 hi))
          simp [hb]
        · exact Finset.sum_nonneg fun j _ ↦ by split_ifs <;> simp [weight_nonneg]
    _ ≤ _ := Finset.sum_le_sum fun i hi ↦
        tail_two_sided (a i) (sq_nonneg _) (ha i (Finset.mem_range.1 hi))

/-- **Babai lift under a prefix floor.** With `0 ≤ gᵢ ≤ ‖bs i‖` on the prefix, the lift failure
probability is at most `Σ_{i<n} 2 exp(−gᵢ²/12)`: the audited Part 47 bound
`Σ 2 exp(−gᵢ²/(4η))` at `η = 3`. -/
theorem liftFail_le_floor {b bs : ℕ → E} (h : IsGSPair b bs) (n : ℕ) {d : ℕ}
    (U : (Fin d → Digit 3) → E) (a : ℕ → Fin d → ℝ)
    (hU : ∀ x, ∀ i < n, inner ℝ (U x) (bs i) = projection (a i) x)
    (ha : ∀ i < n, ∑ c, a i c ^ 2 ≤ ‖bs i‖ ^ 2) (g : ℕ → ℝ) (hg0 : ∀ i < n, 0 ≤ g i)
    (hg : ∀ i < n, g i ≤ ‖bs i‖) :
    ∑ x with LiftFail b bs n (U x), jointWeight x ≤
      ∑ i ∈ Finset.range n, 2 * Real.exp (-g i ^ 2 / 12) := by
  refine (liftFail_le h n U a hU ha).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  have hi := Finset.mem_range.1 hi
  have : g i ^ 2 ≤ ‖bs i‖ ^ 2 := pow_le_pow_left₀ (hg0 i hi) (hg i hi) 2
  gcongr

end SigabaNeo.Wall1.BabaiLift

#print axioms SigabaNeo.Wall1.BabaiLift.gramSchmidt_isGSPair
#print axioms SigabaNeo.Wall1.BabaiLift.babai_sub_mem
#print axioms SigabaNeo.Wall1.BabaiLift.babai_box
#print axioms SigabaNeo.Wall1.BabaiLift.box_unique
#print axioms SigabaNeo.Wall1.BabaiLift.babai_lift
#print axioms SigabaNeo.Wall1.BabaiLift.tail_two_sided
#print axioms SigabaNeo.Wall1.BabaiLift.liftFail_le
#print axioms SigabaNeo.Wall1.BabaiLift.liftFail_le_floor

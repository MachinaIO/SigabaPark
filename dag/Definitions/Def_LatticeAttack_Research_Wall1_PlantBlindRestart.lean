module

public import Definitions.Def_LatticeAttack_Research_Wall1_MultiBlockProduct
import Mathlib.Tactic

set_option autoImplicit true

/-! # Plant-blind restarts on disjoint row blocks (PROOF_GAP Wall 1, Part 134, Theorem 1)

This is the finite form of Theorem 1 of `docs/research/wall1_breakthrough_r1.md`.

The model is as follows.
* The design `x : ι → Y` has the product law with row weight `w`. A row may also carry
  independent per-row coins, by enlarging `Y`.
* The plant `p : P` (for instance `(s, e)`, plus any decoder coins) has law `ρ`, independent of
  the design. The joint law is the product `(∏ⱼ w (x j)) · ρ p`.
* The `k` blocks are given by `b i : Fin (r i) → ι`. They are predetermined and pairwise disjoint,
  which is expressed by injectivity of `⟨i, a⟩ ↦ b i a`.
* Block `i` is accepted when `acc i` holds of its rows. This depends on that block's rows only,
  and in particular is plant-blind.
* If block `i` is decoded, the decoder fails on the event `F i p (rows of block i)`.
* The algorithm decodes the first accepted block. It fails when no block is accepted, or when the
  decoder of the first accepted block fails.

Main results:
* `failProb_eq` (exact law): the failure probability equals
  `∏ᵢ δᵢ + ∑ᵢ (∏_{j<i} δⱼ) · E[1{accᵢ} · Pr_p[Fᵢ]]`.
* `restart_le_avg`: if each block's acceptance-conditioned failure is at most `ε`, then the
  failure probability is at most `∏ δᵢ + ε (1 − ∏ δᵢ)`.
* `restart_le`: the supremum form, failure `≤ ∏ δᵢ + ε*`.
* `restart_le_lift`: the same with an additional lift-error event, failure `≤ ∏ δᵢ + ε* + ℓ*`.
* `restart_le_pow` and `restart_identical`: failure `≤ δ^k + ε*`.
* `restart_le_lwe`: the instance with an iid secret `s` and an iid error `e`, where the decoder
  of block `i` sees `(s, e restricted to block i, rows of block i)`. -/

public section
namespace SigabaNeo.Wall1.PlantBlindRestart
open SigabaNeo.Wall1.MultiBlock Classical

variable {Y ι P : Type*} [Fintype Y] [Fintype ι] [DecidableEq ι] [Fintype P] {k : ℕ}
  {r : Fin k → ℕ}

/-! ## The algorithm -/

/-- The rows of block `i`. -/
@[expose] def block (b : ∀ i, Fin (r i) → ι) (x : ι → Y) (i : Fin k) : Fin (r i) → Y :=
  fun a ↦ x (b i a)

/-- Block `i` is the first accepted block. -/
@[expose] def IsFirst (acc : ∀ i, (Fin (r i) → Y) → Prop) (b : ∀ i, Fin (r i) → ι)
    (x : ι → Y) (i : Fin k) : Prop :=
  acc i (block b x i) ∧ ∀ j < i, ¬ acc j (block b x j)

/-- The restart algorithm fails: no block is accepted, or the decoder run on the first accepted
block fails. -/
@[expose] def Fails (acc : ∀ i, (Fin (r i) → Y) → Prop) (F : ∀ i, P → (Fin (r i) → Y) → Prop)
    (b : ∀ i, Fin (r i) → ι) (x : ι → Y) (p : P) : Prop :=
  (∀ i, ¬ acc i (block b x i)) ∨ ∃ i, IsFirst acc b x i ∧ F i p (block b x i)

omit [Fintype Y] [Fintype ι] [DecidableEq ι] in
theorem isFirst_unique {acc : ∀ i, (Fin (r i) → Y) → Prop} {b : ∀ i, Fin (r i) → ι}
    {x : ι → Y} {i j : Fin k} (hi : IsFirst acc b x i) (hj : IsFirst acc b x j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hi.1 (hj.2 i h)
  · exact h
  · exact absurd hj.1 (hi.2 j h)

omit [Fintype Y] [Fintype ι] [DecidableEq ι] in
theorem exists_isFirst {acc : ∀ i, (Fin (r i) → Y) → Prop} {b : ∀ i, Fin (r i) → ι}
    {x : ι → Y} (h : ∃ i, acc i (block b x i)) : ∃ i, IsFirst acc b x i := by
  let s := Finset.univ.filter fun i ↦ acc i (block b x i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, by simp [s, hi]⟩
  refine ⟨s.min' hs, (Finset.mem_filter.1 (s.min'_mem hs)).2, fun j hj hacc ↦ ?_⟩
  exact absurd (s.min'_le j (by simp [s, hacc])) (not_le.2 hj)

/-! ## Probabilities -/

/-- Probability of an event of the plant. -/
@[expose] noncomputable def plantProb (ρ : P → ℚ) (E : P → Prop) : ℚ :=
  ∑ p, ρ p * if E p then 1 else 0

/-- Failure probability of the restart algorithm under the joint law `w^ι ⊗ ρ`. -/
@[expose] noncomputable def failProb (w : Y → ℚ) (ρ : P → ℚ)
    (acc : ∀ i, (Fin (r i) → Y) → Prop) (F : ∀ i, P → (Fin (r i) → Y) → Prop)
    (b : ∀ i, Fin (r i) → ι) : ℚ :=
  expect w fun x : ι → Y ↦ plantProb ρ (Fails acc F b x)

/-- `δᵢ`: probability that block `i` is rejected. -/
@[expose] noncomputable def rejectProb (w : Y → ℚ) (acc : ∀ i, (Fin (r i) → Y) → Prop)
    (i : Fin k) : ℚ :=
  expect w fun z ↦ if ¬ acc i z then 1 else 0

/-- `1 − δᵢ`: probability that block `i` is accepted. -/
@[expose] noncomputable def acceptProb (w : Y → ℚ) (acc : ∀ i, (Fin (r i) → Y) → Prop)
    (i : Fin k) : ℚ :=
  expect w fun z ↦ if acc i z then 1 else 0

/-- `Pr[accᵢ ∧ Fᵢ]` for block `i` taken alone. Divided by `acceptProb`, it is the conditional
decoding failure `E[Fᵢ | accᵢ]`. -/
@[expose] noncomputable def acceptFail (w : Y → ℚ) (ρ : P → ℚ)
    (acc : ∀ i, (Fin (r i) → Y) → Prop) (F : ∀ i, P → (Fin (r i) → Y) → Prop) (i : Fin k) : ℚ :=
  expect w fun z ↦ (if acc i z then 1 else 0) * plantProb ρ (fun p ↦ F i p z)

/-! ## Expectation calculus -/

section Expect
variable {κ : Type*} [Fintype κ] [DecidableEq κ] {w : Y → ℚ}

private theorem expect_one (hw : ∑ y, w y = 1) : expect w (fun _ : κ → Y ↦ (1 : ℚ)) = 1 := by
  unfold expect
  simp only [mul_one]
  rw [← Fintype.prod_sum (fun (_ : κ) y ↦ w y), hw, Finset.prod_const_one]

private theorem expect_add (G H : (κ → Y) → ℚ) :
    expect w (fun x ↦ G x + H x) = expect w G + expect w H := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

private theorem expect_sum {K : Type*} (s : Finset K) (G : K → (κ → Y) → ℚ) :
    expect w (fun x ↦ ∑ i ∈ s, G i x) = ∑ i ∈ s, expect w (G i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

private theorem expect_const_mul (c : ℚ) (G : (κ → Y) → ℚ) :
    expect w (fun x ↦ c * G x) = c * expect w G := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

private theorem expect_mono (hw0 : ∀ y, 0 ≤ w y) {G H : (κ → Y) → ℚ} (h : ∀ x, G x ≤ H x) :
    expect w G ≤ expect w H :=
  Finset.sum_le_sum fun x _ ↦
    mul_le_mul_of_nonneg_left (h x) (Finset.prod_nonneg fun j _ ↦ hw0 (x j))

private theorem expect_nonneg (hw0 : ∀ y, 0 ≤ w y) {G : (κ → Y) → ℚ} (h : ∀ x, 0 ≤ G x) :
    0 ≤ expect w G := by
  simpa [expect] using expect_mono (κ := κ) hw0 (G := fun _ ↦ 0) h

end Expect

/-! ## Pointwise decomposition of the failure indicator -/

omit [Fintype Y] [Fintype ι] [DecidableEq ι] [Fintype P] in
/-- Failure indicator: either every block is rejected, or exactly one block is the first accepted
one, and then its decoder fails. -/
private theorem fails_indicator (acc : ∀ i, (Fin (r i) → Y) → Prop)
    (F : ∀ i, P → (Fin (r i) → Y) → Prop) (b : ∀ i, Fin (r i) → ι) (x : ι → Y) (p : P) :
    (if Fails acc F b x p then (1 : ℚ) else 0) =
      (∏ i, if ¬ acc i (block b x i) then (1 : ℚ) else 0) +
        ∑ i, (if IsFirst acc b x i then (1 : ℚ) else 0) *
          (if F i p (block b x i) then 1 else 0) := by
  by_cases hne : ∃ i, acc i (block b x i)
  · obtain ⟨i₀, h₀⟩ := exists_isFirst hne
    have hprod : (∏ i, if ¬ acc i (block b x i) then (1 : ℚ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [h₀.1])
    have hsum : (∑ i, (if IsFirst acc b x i then (1 : ℚ) else 0) *
        (if F i p (block b x i) then 1 else 0)) =
        if F i₀ p (block b x i₀) then 1 else 0 := by
      rw [Finset.sum_eq_single i₀ (fun j _ hj ↦ by
        simp [show ¬ IsFirst acc b x j from fun h ↦ hj (isFirst_unique h h₀)]) (by simp)]
      simp [h₀]
    have hiff : Fails acc F b x p ↔ F i₀ p (block b x i₀) := by
      constructor
      · rintro (h | ⟨j, hj, hF⟩)
        · exact absurd h₀.1 (h i₀)
        · rwa [isFirst_unique hj h₀] at hF
      · exact fun h ↦ Or.inr ⟨i₀, h₀, h⟩
    rw [hprod, hsum, zero_add]
    exact if_congr hiff rfl rfl
  · push Not at hne
    have hF : Fails acc F b x p := Or.inl hne
    have hnf (i : Fin k) : ¬ IsFirst acc b x i := fun h ↦ hne i h.1
    simp [hF, hne, hnf]

omit [Fintype Y] [Fintype ι] [DecidableEq ι] in
/-- Averaging over the independent plant: only the decoded block's failure probability remains. -/
private theorem plantProb_fails (ρ : P → ℚ) (hρ : ∑ p, ρ p = 1)
    (acc : ∀ i, (Fin (r i) → Y) → Prop) (F : ∀ i, P → (Fin (r i) → Y) → Prop)
    (b : ∀ i, Fin (r i) → ι) (x : ι → Y) :
    plantProb ρ (Fails acc F b x) =
      (∏ i, if ¬ acc i (block b x i) then (1 : ℚ) else 0) +
        ∑ i, (if IsFirst acc b x i then (1 : ℚ) else 0) *
          plantProb ρ (fun p ↦ F i p (block b x i)) := by
  unfold plantProb
  simp_rw [fails_indicator acc F b x, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hρ,
    one_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun p _ ↦ by ring)

/-! ## Independence across disjoint blocks -/

private theorem prod_split (a c : Fin k → ℚ) (i : Fin k) :
    (∏ j, if j < i then a j else if j = i then c j else 1) =
      (∏ j ∈ Finset.univ.filter (· < i), a j) * c i := by
  rw [Finset.prod_ite, Finset.prod_ite_eq']
  simp

variable {w : Y → ℚ}

/-- Step (1): the probability that every block is rejected is `∏ δᵢ`. -/
private theorem expect_allReject (hw : ∑ y, w y = 1) (acc : ∀ i, (Fin (r i) → Y) → Prop)
    (b : ∀ i, Fin (r i) → ι)
    (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2)) :
    expect w (fun x ↦ ∏ i, if ¬ acc i (block b x i) then (1 : ℚ) else 0) =
      ∏ i, rejectProb w acc i :=
  block_product b hb w hw fun i z ↦ if ¬ acc i z then 1 else 0

/-- Step (1'): block `i` is the first accepted block, weighted by any function of its rows. -/
private theorem expect_isFirst (hw : ∑ y, w y = 1) (acc : ∀ i, (Fin (r i) → Y) → Prop)
    (b : ∀ i, Fin (r i) → ι)
    (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2))
    (f : ∀ i, (Fin (r i) → Y) → ℚ) (i : Fin k) :
    expect w (fun x ↦ (if IsFirst acc b x i then (1 : ℚ) else 0) * f i (block b x i)) =
      (∏ j ∈ Finset.univ.filter (· < i), rejectProb w acc j) *
        expect w (fun z ↦ (if acc i z then 1 else 0) * f i z) := by
  let G : ∀ j, (Fin (r j) → Y) → ℚ := fun j z ↦
    if j < i then (if ¬ acc j z then 1 else 0)
    else if j = i then (if acc j z then 1 else 0) * f j z else 1
  have hpt (x : ι → Y) : (if IsFirst acc b x i then (1 : ℚ) else 0) * f i (block b x i) =
      ∏ j, G j (fun a ↦ x (b j a)) := by
    show _ = ∏ j, G j (block b x j)
    simp only [G]
    rw [prod_split (fun j ↦ if ¬ acc j (block b x j) then 1 else 0)
      (fun j ↦ (if acc j (block b x j) then 1 else 0) * f j (block b x j)) i]
    simp only [Finset.prod_boole, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold IsFirst
    by_cases h1 : acc i (block b x i) <;> by_cases h2 : ∀ j < i, ¬ acc j (block b x j) <;>
      simp [h1, h2]
  have hexp (j : Fin k) : expect w (G j) =
      if j < i then rejectProb w acc j
      else if j = i then expect w (fun z ↦ (if acc j z then 1 else 0) * f j z) else 1 := by
    by_cases h1 : j < i
    · simp [G, h1, rejectProb]
    · by_cases h2 : j = i
      · subst h2; simp [G]
      · simp [G, h1, h2, expect_one hw]
  simp_rw [hpt]
  rw [block_product b hb w hw G]
  simp_rw [hexp]
  exact prod_split _ (fun j ↦ expect w (fun z ↦ (if acc j z then 1 else 0) * f j z)) i

/-! ## Main theorems -/

/-- **Exact law of the restart failure.** Since acceptance is plant-blind and the plant is
independent of the design, the failure probability is
`∏ᵢ δᵢ + ∑ᵢ (∏_{j<i} δⱼ) · Pr[accᵢ ∧ Fᵢ]`. Here `Pr[accᵢ ∧ Fᵢ]` is computed for block `i`
alone, against the unconditioned plant law. -/
theorem failProb_eq (hw : ∑ y, w y = 1) {ρ : P → ℚ} (hρ : ∑ p, ρ p = 1)
    (acc : ∀ i, (Fin (r i) → Y) → Prop) (F : ∀ i, P → (Fin (r i) → Y) → Prop)
    (b : ∀ i, Fin (r i) → ι)
    (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2)) :
    failProb w ρ acc F b = (∏ i, rejectProb w acc i) +
      ∑ i, (∏ j ∈ Finset.univ.filter (· < i), rejectProb w acc j) * acceptFail w ρ acc F i := by
  unfold failProb
  simp_rw [plantProb_fails ρ hρ acc F b]
  rw [expect_add, expect_allReject hw acc b hb, expect_sum]
  exact congrArg _ (Finset.sum_congr rfl fun i _ ↦
    expect_isFirst hw acc b hb (fun i z ↦ plantProb ρ (fun p ↦ F i p z)) i)

/-- The disjoint events "block `i` is the first accepted block" and "no block is accepted" have
total probability one. -/
theorem partition (hw : ∑ y, w y = 1) (acc : ∀ i, (Fin (r i) → Y) → Prop)
    (b : ∀ i, Fin (r i) → ι)
    (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2)) :
    ∑ i, (∏ j ∈ Finset.univ.filter (· < i), rejectProb w acc j) * acceptProb w acc i =
      1 - ∏ i, rejectProb w acc i := by
  have h := failProb_eq (P := Unit) hw (ρ := fun _ ↦ 1) (by simp) acc
    (fun _ _ _ ↦ True) b hb
  have hone : failProb w (fun _ : Unit ↦ (1 : ℚ)) acc (fun _ _ _ ↦ True) b = 1 := by
    unfold failProb
    have (x : ι → Y) : plantProb (fun _ : Unit ↦ (1 : ℚ)) (Fails acc (fun _ _ _ ↦ True) b x)
        = 1 := by
      unfold plantProb
      by_cases hne : ∃ i, acc i (block b x i)
      · obtain ⟨i, hi⟩ := exists_isFirst hne
        simp [show Fails acc (fun _ _ _ ↦ True) b x () from Or.inr ⟨i, hi, trivial⟩]
      · push Not at hne
        simp [show Fails acc (fun _ _ _ ↦ True) b x () from Or.inl hne]
    simp_rw [this]
    exact expect_one hw
  have hacc (i : Fin k) :
      acceptFail w (fun _ : Unit ↦ (1 : ℚ)) acc (fun _ _ _ ↦ True) i = acceptProb w acc i := by
    simp [acceptFail, acceptProb, plantProb]
  simp_rw [hacc] at h
  linarith

/-- **Theorem 1, averaged form.** Suppose that for every block the acceptance-conditioned decoding
failure is at most `ε`, i.e. `Pr[accᵢ ∧ Fᵢ] ≤ ε · Pr[accᵢ]`. Then the failure probability is at
most `∏ δᵢ + ε · (1 − ∏ δᵢ)`. -/
theorem restart_le_avg (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y) {ρ : P → ℚ}
    (hρ : ∑ p, ρ p = 1) (acc : ∀ i, (Fin (r i) → Y) → Prop)
    (F : ∀ i, P → (Fin (r i) → Y) → Prop) (b : ∀ i, Fin (r i) → ι)
    (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2)) {ε : ℚ}
    (hε : ∀ i, acceptFail w ρ acc F i ≤ ε * acceptProb w acc i) :
    failProb w ρ acc F b ≤ (∏ i, rejectProb w acc i) + ε * (1 - ∏ i, rejectProb w acc i) := by
  rw [failProb_eq hw hρ acc F b hb, ← partition hw acc b hb, Finset.mul_sum]
  refine add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦ ?_)
  have hc : 0 ≤ ∏ j ∈ Finset.univ.filter (· < i), rejectProb w acc j :=
    Finset.prod_nonneg fun j _ ↦ expect_nonneg hw0 fun _ ↦ by positivity
  calc _ ≤ (∏ j ∈ Finset.univ.filter (· < i), rejectProb w acc j) * (ε * acceptProb w acc i) :=
        mul_le_mul_of_nonneg_left (hε i) hc
    _ = _ := by ring

theorem rejectProb_nonneg (hw0 : ∀ y, 0 ≤ w y) (acc : ∀ i, (Fin (r i) → Y) → Prop) (i : Fin k) :
    0 ≤ rejectProb w acc i :=
  expect_nonneg hw0 fun _ ↦ by positivity

/-- **Theorem 1, supremum form.** If, for every block `i` and every value of its rows that passes
`acc i`, the plant failure probability of the decoder is at most `ε`, then
`Pr[fail] ≤ ∏ δᵢ + ε (1 − ∏ δᵢ) ≤ ∏ δᵢ + ε`. -/
theorem restart_le (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y) {ρ : P → ℚ}
    (hρ : ∑ p, ρ p = 1) (acc : ∀ i, (Fin (r i) → Y) → Prop)
    (F : ∀ i, P → (Fin (r i) → Y) → Prop) (b : ∀ i, Fin (r i) → ι)
    (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2)) {ε : ℚ} (hε0 : 0 ≤ ε)
    (hε : ∀ i z, acc i z → plantProb ρ (fun p ↦ F i p z) ≤ ε) :
    failProb w ρ acc F b ≤ (∏ i, rejectProb w acc i) + ε := by
  have h := restart_le_avg hw hw0 hρ acc F b hb (ε := ε) fun i ↦ by
    unfold acceptFail acceptProb
    rw [← expect_const_mul]
    refine expect_mono hw0 fun z ↦ ?_
    by_cases ha : acc i z
    · simpa [ha] using hε i z ha
    · simp [ha]
  have hp : 0 ≤ ∏ i, rejectProb w acc i :=
    Finset.prod_nonneg fun i _ ↦ rejectProb_nonneg hw0 acc i
  nlinarith

/-- **Theorem 1 with the lift error.** The decoder of block `i` fails if the projected plant is not
the unique shortest pair (event `U i`, probability `≤ ε*` on accepted rows), or if the Babai lift
fails (event `Lf i`, probability `≤ ℓ*` on accepted rows). Then
`Pr[fail] ≤ ∏ δᵢ + ε* + ℓ*`. -/
theorem restart_le_lift (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y) {ρ : P → ℚ}
    (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p) (acc : ∀ i, (Fin (r i) → Y) → Prop)
    (U Lf : ∀ i, P → (Fin (r i) → Y) → Prop) (b : ∀ i, Fin (r i) → ι)
    (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2)) {ε ℓ : ℚ}
    (hε0 : 0 ≤ ε) (hℓ0 : 0 ≤ ℓ)
    (hε : ∀ i z, acc i z → plantProb ρ (fun p ↦ U i p z) ≤ ε)
    (hℓ : ∀ i z, acc i z → plantProb ρ (fun p ↦ Lf i p z) ≤ ℓ) :
    failProb w ρ acc (fun i p z ↦ U i p z ∨ Lf i p z) b ≤ (∏ i, rejectProb w acc i) + (ε + ℓ) := by
  refine restart_le hw hw0 hρ acc _ b hb (add_nonneg hε0 hℓ0) fun i z hz ↦ ?_
  refine le_trans ?_ (add_le_add (hε i z hz) (hℓ i z hz))
  unfold plantProb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ ↦ ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hρ0 p)
  by_cases h1 : U i p z <;> by_cases h2 : Lf i p z <;> simp [h1, h2]

/-- **Corollary 1.1.** If every block is rejected with probability at most `δ`, then
`Pr[fail] ≤ δ^k + ε*`. -/
theorem restart_le_pow (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y) {ρ : P → ℚ}
    (hρ : ∑ p, ρ p = 1) (acc : ∀ i, (Fin (r i) → Y) → Prop)
    (F : ∀ i, P → (Fin (r i) → Y) → Prop) (b : ∀ i, Fin (r i) → ι)
    (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2)) {δ ε : ℚ} (hε0 : 0 ≤ ε)
    (hδ : ∀ i, rejectProb w acc i ≤ δ)
    (hε : ∀ i z, acc i z → plantProb ρ (fun p ↦ F i p z) ≤ ε) :
    failProb w ρ acc F b ≤ δ^k + ε := by
  have h := restart_le hw hw0 hρ acc F b hb hε0 hε
  have hp : (∏ i, rejectProb w acc i) ≤ ∏ _i : Fin k, δ :=
    Finset.prod_le_prod₀ (fun i _ ↦ rejectProb_nonneg hw0 acc i) fun i _ ↦ hδ i
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  linarith

/-- **Identical blocks.** With `k` blocks of the same size `r₀`, the same acceptance predicate
`acc₀` and rejection probability `δ₀`, `Pr[fail] ≤ δ₀^k + ε*`. -/
theorem restart_identical (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y) {ρ : P → ℚ}
    (hρ : ∑ p, ρ p = 1) {r₀ : ℕ} (acc₀ : (Fin r₀ → Y) → Prop)
    (F : ∀ _ : Fin k, P → (Fin r₀ → Y) → Prop) (b : Fin k → Fin r₀ → ι)
    (hb : Function.Injective (fun q : (Σ _ : Fin k, Fin r₀) ↦ b q.1 q.2)) {ε : ℚ} (hε0 : 0 ≤ ε)
    (hε : ∀ i z, acc₀ z → plantProb ρ (fun p ↦ F i p z) ≤ ε) :
    failProb w ρ (fun _ ↦ acc₀) F b ≤
      (expect w fun z ↦ if ¬ acc₀ z then (1 : ℚ) else 0)^k + ε :=
  restart_le_pow (r := fun _ ↦ r₀) hw hw0 hρ (fun _ ↦ acc₀) F b hb hε0 (fun _ ↦ le_rfl) hε

/-! ## Instance: iid secret and error, decoder sees its own error block -/

/-- The product law of an iid secret `s : Fin n → S` and an iid error `e : ι → S`. -/
@[expose] noncomputable def plantWeight {S : Type*} [Fintype S] (n : ℕ) (ν : S → ℚ)
    (p : (Fin n → S) × (ι → S)) : ℚ :=
  (∏ j, ν (p.1 j)) * ∏ j, ν (p.2 j)

theorem plantWeight_sum {S : Type*} [Fintype S] (n : ℕ) {ν : S → ℚ} (hν : ∑ a, ν a = 1) :
    ∑ p, plantWeight (ι := ι) n ν p = 1 := by
  simp only [plantWeight, Fintype.sum_prod_type, ← Finset.sum_mul, ← Finset.mul_sum]
  have h1 := expect_one (κ := Fin n) hν
  have h2 := expect_one (κ := ι) hν
  simp only [expect, mul_one] at h1 h2
  rw [h1, h2, mul_one]

/-- Uniform row weight (for a uniform design, with uniform per-row coins if `Y` carries them). -/
theorem uniform_sum [Nonempty Y] : ∑ _y : Y, (1 / Fintype.card Y : ℚ) = 1 := by
  simp [Finset.card_univ]

/-- **Theorem 1 for LWE-shaped data.** The secret `s` and the error `e` are iid with weight `ν`,
independent of the design. The decoder of block `i` fails on the event
`Fdec i s (e restricted to block i) (rows of block i)`. If that event has probability at most `ε`
whenever the rows of block `i` pass `acc i`, then `Pr[fail] ≤ ∏ δᵢ + ε`. -/
theorem restart_le_lwe {S : Type*} [Fintype S] {n : ℕ} {ν : S → ℚ} (hν : ∑ a, ν a = 1)
    (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y) (acc : ∀ i, (Fin (r i) → Y) → Prop)
    (Fdec : ∀ i, (Fin n → S) → (Fin (r i) → S) → (Fin (r i) → Y) → Prop)
    (b : ∀ i, Fin (r i) → ι)
    (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2)) {ε : ℚ} (hε0 : 0 ≤ ε)
    (hε : ∀ i z, acc i z →
      plantProb (plantWeight n ν) (fun p ↦ Fdec i p.1 (fun a ↦ p.2 (b i a)) z) ≤ ε) :
    failProb w (plantWeight n ν) acc (fun i p z ↦ Fdec i p.1 (fun a ↦ p.2 (b i a)) z) b ≤
      (∏ i, rejectProb w acc i) + ε :=
  restart_le hw hw0 (plantWeight_sum n hν) acc _ b hb hε0 hε

end SigabaNeo.Wall1.PlantBlindRestart

#print axioms SigabaNeo.Wall1.PlantBlindRestart.failProb_eq
#print axioms SigabaNeo.Wall1.PlantBlindRestart.partition
#print axioms SigabaNeo.Wall1.PlantBlindRestart.restart_le_avg
#print axioms SigabaNeo.Wall1.PlantBlindRestart.restart_le
#print axioms SigabaNeo.Wall1.PlantBlindRestart.restart_le_lift
#print axioms SigabaNeo.Wall1.PlantBlindRestart.restart_le_pow
#print axioms SigabaNeo.Wall1.PlantBlindRestart.restart_identical
#print axioms SigabaNeo.Wall1.PlantBlindRestart.restart_le_lwe

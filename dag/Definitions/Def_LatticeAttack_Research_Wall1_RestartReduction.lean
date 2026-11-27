module

public import Definitions.Def_LatticeAttack_Research_Wall1_PlantBlindRestart
public import Definitions.Def_LatticeAttack_Research_Wall1_ConditionalReduction
import all Definitions.Def_LatticeAttack_Research_Wall1_ConditionalReduction
import all Definitions.Def_LatticeAttack_Research_Wall1_UniquenessProbability
import all Definitions.Def_LatticeAttack_Research_Wall1_ShiftedTheta
import Mathlib.Tactic

set_option autoImplicit true

/-! # Concrete restart reduction (PROOF_GAP Wall 1, Part 134 applied to Part 94 / Part 47 data)

This file instantiates the abstract plant-blind restart theorem (`PlantBlindRestart.failProb_eq`,
`restart_le`, `restart_le_lift`) with the concrete final-block test of
`ConditionalReduction.lean`.

Setting.
* Design rows `x : ι → Y` with product law `w` (per-row coins can be folded into `Y`), and `k`
  predetermined pairwise disjoint row blocks `b i : Fin (r i) → ι`.
* A plant-free reducer: for each block `i`, `R i` maps the rows of that block to a
  `FinalBlock (N i) (d i)`.
* The plant `p : P` has a law `ρ` independent of the design. Block `i` decodes against the
  CBD(3) vector `π i p : Fin (N i) → Digit 3`. The only requirement on `π i` is that its marginal
  is the product CBD(3) law `jointWeight` (hypothesis `hπ`). For LWE this is `(s, e restricted to
  block i)`, which is a product CBD vector since the coordinates are distinct.
* Acceptance of block `i` is the concrete test `(R i z).Good (g i) (L i)`, i.e. GS floor `≥ g i` and
  horizontal minimum `≥ L i`, together with an extra block-only predicate `Pre i z` (the prefix
  GS floor of the Babai lift, Part 47; take `Pre := fun _ _ ↦ True` if not needed).
* Block `i` fails to decode when the projected plant is not all-heights unique (Part 94 criterion,
  `allHeightsUnique`) or when the lift fails (event `Lf i p z`).

No Babai-lift lemma is formalized in the repository. The lift error is therefore the explicit
hypothesis `hℓ`: on accepted rows, `Pr_p[Lf i p z] ≤ ℓ`. Part 47's audit gives
`ℓ = Σ_{i ≤ j} 2 exp(−gᵢ²/(4η))` on the prefix floor.

Main results.
* `plantProb_not_unique`: for one block, the plant probability of non-uniqueness is exactly
  `1 − (R i z).success`.
* `restartReduction_avg`: `Pr[fail] ≤ ∏ δᵢ + (ε + ℓ)(1 − ∏ δᵢ)`.
* `restartReduction`: `Pr[fail] ≤ ∏ δᵢ + ε + ℓ`, where `ε ≥ reductionError (N i) (d i) (g i) (L i)`
  for every block.
* `restartReduction_uniform`: identical shapes, `Pr[fail] ≤ ∏ δᵢ + reductionError N d g L + ℓ`.
* `restartReduction_single`: the case `k = 1`, `Pr[success] ≥ (1 − δ)(1 − ε − ℓ)`, the analogue of
  `conditionalReduction`. -/

public section
namespace SigabaNeo.Wall1.RestartReduction
open SigabaNeo.Wall1 SigabaNeo.Wall1.MultiBlock SigabaNeo.Wall1.PlantBlindRestart
open SampleDeletion CBDTail Classical

variable {Y ι P : Type*} [Fintype Y] [Fintype ι] [DecidableEq ι] [Fintype P] {k : ℕ}
  {r : Fin k → ℕ} {N d : Fin k → ℕ}

/-! ## The concrete acceptance test and decoding failure -/

/-- Concrete plant-blind acceptance of block `i`: the final block passes the GS floor `g i` and the
horizontal minimum `L i`, and the rows satisfy the extra block-only predicate `Pre i`. -/
@[expose] def accept (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i)) (g L : Fin k → ℝ)
    (Pre : ∀ i, (Fin (r i) → Y) → Prop) (i : Fin k) (z : Fin (r i) → Y) : Prop :=
  (R i z).Good (g i) (L i) ∧ Pre i z

/-- The projected plant of block `i` is the all-heights unique shortest pair of its final block. -/
@[expose] def Unique (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i))
    (π : ∀ i, P → Fin (N i) → Digit 3) (i : Fin k) (p : P) (z : Fin (r i) → Y) : Prop :=
  allHeightsUnique (horizontalLattice (R i z).V (R i z).basis) (projectedCBD (R i z).Q (π i p))

/-- Decoding block `i` fails: non-uniqueness, or failure of the lift. -/
@[expose] def decodeFail (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i))
    (π : ∀ i, P → Fin (N i) → Digit 3) (Lf : ∀ i, P → (Fin (r i) → Y) → Prop)
    (i : Fin k) (p : P) (z : Fin (r i) → Y) : Prop :=
  ¬ Unique R π i p z ∨ Lf i p z

/-! ## One block: the plant probability of non-uniqueness -/

omit [Fintype Y] [Fintype ι] [DecidableEq ι] in
/-- If the block-`i` plant has the product CBD(3) marginal, then for fixed rows `z` the plant
probability of non-uniqueness is exactly `1 − (R i z).success`. -/
theorem plantProb_not_unique {ρ : P → ℚ} (hρ : ∑ p, ρ p = 1)
    (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i)) (π : ∀ i, P → Fin (N i) → Digit 3)
    (i : Fin k) (hπ : ∀ v, ((∑ p with π i p = v, ρ p : ℚ) : ℝ) = jointWeight v)
    (z : Fin (r i) → Y) :
    (plantProb ρ (fun p ↦ ¬ Unique R π i p z) : ℝ) = 1 - (R i z).success := by
  have fiber (f : (Fin (N i) → Digit 3) → ℝ) :
      ∑ p, (ρ p : ℝ) * f (π i p) = ∑ v, jointWeight v * f v := by
    rw [← Finset.sum_fiberwise Finset.univ (π i) (fun p ↦ (ρ p : ℝ) * f (π i p))]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [← hπ v, Rat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [(Finset.mem_filter.1 hp).2]
  have hone : ∑ v : Fin (N i) → Digit 3, jointWeight v = 1 := by
    have := fiber fun _ ↦ 1
    simp only [mul_one] at this
    rw [← this, ← Rat.cast_sum, hρ, Rat.cast_one]
  unfold plantProb FinalBlock.success Unique
  simp only [Rat.cast_sum, Rat.cast_mul, apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_one, Rat.cast_zero]
  rw [fiber (fun v ↦ if ¬ allHeightsUnique (horizontalLattice (R i z).V (R i z).basis)
    (projectedCBD (R i z).Q v) then 1 else 0), Finset.sum_filter, ← hone,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  split_ifs <;> simp_all

/-- `reductionError` is nonnegative for a positive GS floor. -/
theorem reductionError_nonneg {N d : ℕ} {g L : ℝ} (hg : 0 < g) :
    0 ≤ reductionError N d g L := by
  have theta (k : ℝ) (hk : 0 < k) : 0 ≤ thetaExcess d g k := by
    apply sub_nonneg.mpr
    apply one_le_pow₀
    have h := (gaussian_summable (show 0 < g^2/(12*k^2) by positivity)).le_tsum
      (0 : ℤ) (fun i _ ↦ (Real.exp_pos _).le)
    simpa using h
  dsimp only [reductionError]
  apply add_nonneg (add_nonneg (by positivity) (theta 1 one_pos))
  apply Finset.sum_nonneg
  intro k hk
  exact theta k (by exact_mod_cast (show 0 < k by have := (Finset.mem_Icc.mp hk).1; omega))

omit [Fintype Y] [Fintype ι] [DecidableEq ι] in
/-- **One accepted block.** On rows that pass the concrete test, the decoder fails with plant
probability at most `reductionError (N i) (d i) (g i) (L i) + ℓ`. This is `uniquenessProbability`
plus a union bound with the lift event. -/
theorem plantProb_decodeFail_le {ρ : P → ℚ} (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p)
    (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i)) (π : ∀ i, P → Fin (N i) → Digit 3)
    (Lf : ∀ i, P → (Fin (r i) → Y) → Prop) {g L : Fin k → ℝ}
    (Pre : ∀ i, (Fin (r i) → Y) → Prop) (i : Fin k)
    (hπ : ∀ v, ((∑ p with π i p = v, ρ p : ℚ) : ℝ) = jointWeight v)
    (hg : 0 < g i) (hL : 0 ≤ L i) (gap : 0 < L i ^ 2 - 1 - (3/2) * (d i : ℝ))
    {z : Fin (r i) → Y} (hz : accept R g L Pre i z) {ℓ : ℝ}
    (hℓ : (plantProb ρ (fun p ↦ Lf i p z) : ℝ) ≤ ℓ) :
    (plantProb ρ (fun p ↦ decodeFail R π Lf i p z) : ℝ) ≤
      reductionError (N i) (d i) (g i) (L i) + ℓ := by
  have union : plantProb ρ (fun p ↦ decodeFail R π Lf i p z) ≤
      plantProb ρ (fun p ↦ ¬ Unique R π i p z) + plantProb ρ (fun p ↦ Lf i p z) := by
    unfold plantProb decodeFail
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ ↦ ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (hρ0 p)
    by_cases h1 : Unique R π i p z <;> by_cases h2 : Lf i p z <;> simp [h1, h2]
  have hu : 1 - reductionError (N i) (d i) (g i) (L i) ≤ (R i z).success :=
    uniquenessProbability _ (R i z).symmetric (R i z).idempotent (R i z).trace_eq _
      (R i z).fixed _ hg hz.1.1 hL hz.1.2 gap
  have hc := (Rat.cast_le (K := ℝ)).2 union
  rw [Rat.cast_add, plantProb_not_unique hρ R π i hπ z] at hc
  linarith

/-! ## The restart bound with a real-valued per-block error -/

/-- The abstract restart law (`failProb_eq`, `partition`) read in `ℝ`: if every accepted block
fails to decode with plant probability at most `η`, then
`Pr[fail] ≤ ∏ δᵢ + η (1 − ∏ δᵢ)`. -/
theorem failProb_le_real {w : Y → ℚ} (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y) {ρ : P → ℚ}
    (hρ : ∑ p, ρ p = 1) (acc : ∀ i, (Fin (r i) → Y) → Prop)
    (F : ∀ i, P → (Fin (r i) → Y) → Prop) (b : ∀ i, Fin (r i) → ι)
    (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2)) {η : ℝ}
    (hη : ∀ i z, acc i z → (plantProb ρ (fun p ↦ F i p z) : ℝ) ≤ η) :
    (failProb w ρ acc F b : ℝ) ≤
      (∏ i, (rejectProb w acc i : ℝ)) + η * (1 - ∏ i, (rejectProb w acc i : ℝ)) := by
  have e := congrArg (Rat.cast : ℚ → ℝ) (failProb_eq hw hρ acc F b hb)
  have pt := congrArg (Rat.cast : ℚ → ℝ) (partition hw acc b hb)
  simp only [Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
    Rat.cast_one] at e pt
  rw [e, ← pt, Finset.mul_sum]
  refine add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦ ?_)
  have hc : (0 : ℝ) ≤ ∏ j ∈ Finset.univ.filter (· < i), (rejectProb w acc j : ℝ) :=
    Finset.prod_nonneg fun j _ ↦ by exact_mod_cast rejectProb_nonneg hw0 acc j
  have hAF : (acceptFail w ρ acc F i : ℝ) ≤ η * acceptProb w acc i := by
    unfold acceptFail acceptProb expect
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_prod, apply_ite (Rat.cast : ℚ → ℝ),
      Rat.cast_one, Rat.cast_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ ↦ ?_
    have hz : (0 : ℝ) ≤ ∏ j, (w (z j) : ℝ) :=
      Finset.prod_nonneg fun j _ ↦ by exact_mod_cast hw0 _
    by_cases ha : acc i z
    · simp only [ha, ite_true, one_mul, mul_one]
      nlinarith [hη i z ha]
    · simp [ha]
  calc _ ≤ (∏ j ∈ Finset.univ.filter (· < i), (rejectProb w acc j : ℝ)) *
        (η * acceptProb w acc i) := mul_le_mul_of_nonneg_left hAF hc
    _ = _ := by ring

/-! ## Main theorems -/

/-- **Concrete restart reduction, averaged form.** `k` disjoint row blocks, a plant-free reducer
`R i` per block, acceptance by the concrete test (GS floor `g i`, minimum `L i`, extra block-only
predicate `Pre i`), and a plant whose block-`i` CBD vector `π i` has the product CBD(3) marginal.
If `reductionError (N i) (d i) (g i) (L i) ≤ ε` for every block and the lift fails with plant
probability `≤ ℓ` on accepted rows, then
`Pr[fail] ≤ ∏ δᵢ + (ε + ℓ)(1 − ∏ δᵢ)`, where `δᵢ = rejectProb w (accept R g L Pre) i`. -/
theorem restartReduction_avg {w : Y → ℚ} (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    {ρ : P → ℚ} (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p)
    (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i)) (π : ∀ i, P → Fin (N i) → Digit 3)
    (hπ : ∀ i v, ((∑ p with π i p = v, ρ p : ℚ) : ℝ) = jointWeight v)
    (Lf : ∀ i, P → (Fin (r i) → Y) → Prop) (Pre : ∀ i, (Fin (r i) → Y) → Prop)
    {g L : Fin k → ℝ} (hg : ∀ i, 0 < g i) (hL : ∀ i, 0 ≤ L i)
    (gap : ∀ i, 0 < L i ^ 2 - 1 - (3/2) * (d i : ℝ))
    (b : ∀ i, Fin (r i) → ι) (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2))
    {ε ℓ : ℝ} (hε : ∀ i, reductionError (N i) (d i) (g i) (L i) ≤ ε)
    (hℓ : ∀ i z, accept R g L Pre i z → (plantProb ρ (fun p ↦ Lf i p z) : ℝ) ≤ ℓ) :
    (failProb w ρ (accept R g L Pre) (decodeFail R π Lf) b : ℝ) ≤
      (∏ i, (rejectProb w (accept R g L Pre) i : ℝ)) +
        (ε + ℓ) * (1 - ∏ i, (rejectProb w (accept R g L Pre) i : ℝ)) :=
  failProb_le_real hw hw0 hρ _ _ b hb fun i z hz ↦
    (plantProb_decodeFail_le hρ hρ0 R π Lf Pre i (hπ i) (hg i) (hL i) (gap i) hz
      (hℓ i z hz)).trans (by linarith [hε i])

/-- **Concrete restart reduction.** Under the hypotheses of `restartReduction_avg`, with
`ε, ℓ ≥ 0`: `Pr[fail] ≤ ∏ δᵢ + ε + ℓ`. This is Theorem 1 of `wall1_breakthrough_r1.md` with the
uniqueness error supplied by `uniquenessProbability`. -/
theorem restartReduction {w : Y → ℚ} (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    {ρ : P → ℚ} (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p)
    (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i)) (π : ∀ i, P → Fin (N i) → Digit 3)
    (hπ : ∀ i v, ((∑ p with π i p = v, ρ p : ℚ) : ℝ) = jointWeight v)
    (Lf : ∀ i, P → (Fin (r i) → Y) → Prop) (Pre : ∀ i, (Fin (r i) → Y) → Prop)
    {g L : Fin k → ℝ} (hg : ∀ i, 0 < g i) (hL : ∀ i, 0 ≤ L i)
    (gap : ∀ i, 0 < L i ^ 2 - 1 - (3/2) * (d i : ℝ))
    (b : ∀ i, Fin (r i) → ι) (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2))
    {ε ℓ : ℝ} (hε0 : 0 ≤ ε) (hℓ0 : 0 ≤ ℓ)
    (hε : ∀ i, reductionError (N i) (d i) (g i) (L i) ≤ ε)
    (hℓ : ∀ i z, accept R g L Pre i z → (plantProb ρ (fun p ↦ Lf i p z) : ℝ) ≤ ℓ) :
    (failProb w ρ (accept R g L Pre) (decodeFail R π Lf) b : ℝ) ≤
      (∏ i, (rejectProb w (accept R g L Pre) i : ℝ)) + ε + ℓ := by
  have h := restartReduction_avg hw hw0 hρ hρ0 R π hπ Lf Pre hg hL gap b hb hε hℓ
  have hp : (0 : ℝ) ≤ ∏ i, (rejectProb w (accept R g L Pre) i : ℝ) :=
    Finset.prod_nonneg fun i _ ↦ by exact_mod_cast rejectProb_nonneg hw0 _ i
  nlinarith

/-- **Identical block shapes.** All final blocks live in `FinalBlock N d` and share the floor `g`
and minimum `L`. Then `Pr[fail] ≤ ∏ δᵢ + reductionError N d g L + ℓ`. -/
theorem restartReduction_uniform {w : Y → ℚ} (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    {ρ : P → ℚ} (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p) {N d : ℕ}
    (R : ∀ i, (Fin (r i) → Y) → FinalBlock N d) (π : Fin k → P → Fin N → Digit 3)
    (hπ : ∀ i v, ((∑ p with π i p = v, ρ p : ℚ) : ℝ) = jointWeight v)
    (Lf : ∀ i, P → (Fin (r i) → Y) → Prop) (Pre : ∀ i, (Fin (r i) → Y) → Prop)
    {g L : ℝ} (hg : 0 < g) (hL : 0 ≤ L) (gap : 0 < L ^ 2 - 1 - (3/2) * (d : ℝ))
    (b : ∀ i, Fin (r i) → ι) (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2))
    {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ)
    (hℓ : ∀ i z, accept (N := fun _ ↦ N) (d := fun _ ↦ d) R (fun _ ↦ g) (fun _ ↦ L) Pre i z →
      (plantProb ρ (fun p ↦ Lf i p z) : ℝ) ≤ ℓ) :
    (failProb w ρ (accept (N := fun _ ↦ N) (d := fun _ ↦ d) R (fun _ ↦ g) (fun _ ↦ L) Pre)
        (decodeFail (N := fun _ ↦ N) (d := fun _ ↦ d) R π Lf) b : ℝ) ≤
      (∏ i, (rejectProb w
        (accept (N := fun _ ↦ N) (d := fun _ ↦ d) R (fun _ ↦ g) (fun _ ↦ L) Pre) i : ℝ)) +
        reductionError N d g L + ℓ :=
  restartReduction (N := fun _ ↦ N) (d := fun _ ↦ d) hw hw0 hρ hρ0 R π hπ Lf Pre
    (fun _ ↦ hg) (fun _ ↦ hL) (fun _ ↦ gap) b hb (reductionError_nonneg hg) hℓ0
    (fun _ ↦ le_rfl) hℓ

/-- **One block (`k = 1`): the analogue of `conditionalReduction`.** With `δ` the rejection
probability of the single block and `ε ≥ reductionError`, the success probability is at least
`(1 − δ)(1 − (ε + ℓ))`. -/
theorem restartReduction_single {w : Y → ℚ} (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    {ρ : P → ℚ} (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p) {r : Fin 1 → ℕ} {N d : Fin 1 → ℕ}
    (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i)) (π : ∀ i, P → Fin (N i) → Digit 3)
    (hπ : ∀ i v, ((∑ p with π i p = v, ρ p : ℚ) : ℝ) = jointWeight v)
    (Lf : ∀ i, P → (Fin (r i) → Y) → Prop) (Pre : ∀ i, (Fin (r i) → Y) → Prop)
    {g L : Fin 1 → ℝ} (hg : ∀ i, 0 < g i) (hL : ∀ i, 0 ≤ L i)
    (gap : ∀ i, 0 < L i ^ 2 - 1 - (3/2) * (d i : ℝ))
    (b : ∀ i, Fin (r i) → ι) (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2))
    {ε ℓ : ℝ} (hε : ∀ i, reductionError (N i) (d i) (g i) (L i) ≤ ε)
    (hℓ : ∀ i z, accept R g L Pre i z → (plantProb ρ (fun p ↦ Lf i p z) : ℝ) ≤ ℓ) :
    (1 - (rejectProb w (accept R g L Pre) 0 : ℝ)) * (1 - (ε + ℓ)) ≤
      1 - (failProb w ρ (accept R g L Pre) (decodeFail R π Lf) b : ℝ) := by
  have h := restartReduction_avg hw hw0 hρ hρ0 R π hπ Lf Pre hg hL gap b hb hε hℓ
  rw [Fin.prod_univ_one] at h
  nlinarith

/-! ## LWE instance: the block plant `(s, e restricted to block i)` has the CBD marginal -/

/-- The CBD(3) weight, as a rational. -/
@[expose] def cbdQ (a : Digit 3) : ℚ := (mass a : ℚ) / 64

theorem cbdQ_sum : ∑ a, cbdQ a = 1 := by
  simp [cbdQ, Fin.sum_univ_succ, mass, Nat.choose]
  norm_num

theorem cbdQ_nonneg (a : Digit 3) : 0 ≤ cbdQ a := by
  unfold cbdQ
  positivity

/-- The CBD vector of block `i` for an LWE plant `(s, e)`: the secret and the error restricted to
the rows of block `i`, laid out in `Fin (N i)` by `σ i`. -/
@[expose] def lwePlant {n : ℕ} (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i)) (b : ∀ i, Fin (r i) → ι)
    (i : Fin k) (p : (Fin n → Digit 3) × (ι → Digit 3)) : Fin (N i) → Digit 3 :=
  fun a ↦ Sum.elim p.1 (fun c ↦ p.2 (b i c)) (σ i a)

omit [Fintype ι] [DecidableEq ι] in
private theorem lwePlant_eq_iff {n : ℕ} (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i))
    (b : ∀ i, Fin (r i) → ι) (i : Fin k) (v : Fin (N i) → Digit 3) (s : Fin n → Digit 3)
    (e : ι → Digit 3) :
    lwePlant σ b i (s, e) = v ↔
      s = (fun j ↦ v ((σ i).symm (.inl j))) ∧ ∀ c, e (b i c) = v ((σ i).symm (.inr c)) := by
  constructor
  · rintro rfl
    exact ⟨funext fun j ↦ by simp [lwePlant], fun c ↦ by simp [lwePlant]⟩
  · rintro ⟨rfl, he⟩
    funext a
    rcases hx : σ i a with j | c
    · simp only [lwePlant, hx, Sum.elim_inl]
      rw [← hx, Equiv.symm_apply_apply]
    · simp only [lwePlant, hx, Sum.elim_inr]
      rw [he c, ← hx, Equiv.symm_apply_apply]

/-- **Marginal of the LWE block plant.** If the secret and the error are iid CBD(3) and the rows of
block `i` are distinct, then `(s, e restricted to block i)` has the product CBD(3) law. This
discharges the hypothesis `hπ` of `restartReduction`. -/
theorem lwePlant_marginal {n : ℕ} (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i))
    (b : ∀ i, Fin (r i) → ι) (i : Fin k) (hbi : Function.Injective (b i))
    (v : Fin (N i) → Digit 3) :
    ((∑ p with lwePlant σ b i p = v, plantWeight n cbdQ p : ℚ) : ℝ) = jointWeight v := by
  let s0 : Fin n → Digit 3 := fun j ↦ v ((σ i).symm (.inl j))
  let t : Fin (r i) → Digit 3 := fun c ↦ v ((σ i).symm (.inr c))
  -- the error part, by independence of the distinct coordinates `b i c`
  have herr : (∑ e : ι → Digit 3, (∏ j, cbdQ (e j)) *
      ∏ c, (if e (b i c) = t c then (1 : ℚ) else 0)) = ∏ c, cbdQ (t c) := by
    have hb' : Function.Injective
        (fun q : (Σ _ : Fin (r i), Fin 1) ↦ (fun c (_ : Fin 1) ↦ b i c) q.1 q.2) := by
      rintro ⟨c₁, a₁⟩ ⟨c₂, a₂⟩ h
      have := hbi h
      subst this
      rw [Subsingleton.elim a₁ a₂]
    have := block_product (r := fun _ ↦ 1) (fun c (_ : Fin 1) ↦ b i c) hb' cbdQ cbdQ_sum
      (fun c z ↦ if z 0 = t c then 1 else 0)
    unfold expect at this
    rw [this]
    refine Finset.prod_congr rfl fun c _ ↦ ?_
    rw [← (Equiv.funUnique (Fin 1) (Digit 3)).symm.sum_comp]
    simp
  have hsum : (∑ p with lwePlant σ b i p = v, plantWeight n cbdQ p) =
      (∏ j, cbdQ (s0 j)) * ∏ c, cbdQ (t c) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp_rw [lwePlant_eq_iff σ b i v]
    rw [Finset.sum_eq_single s0 (fun s _ hs ↦ by simp [s0, hs]) (by simp), ← herr,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    simp only [Finset.prod_boole, Finset.mem_univ, true_implies, plantWeight, s0, t]
    split_ifs with h1 h2 h2 <;> simp_all
  rw [hsum, jointWeight, ← (σ i).symm.prod_comp, Fintype.prod_sum_type]
  simp [cbdQ, weight, s0, t]

/-- **Concrete restart reduction for LWE-shaped data.** The secret `s : Fin n → Digit 3` and the
error `e : ι → Digit 3` are iid CBD(3), independent of the design. Block `i` decodes against
`(s, e restricted to block i)`. Then `Pr[fail] ≤ ∏ δᵢ + ε + ℓ`, with no marginal hypothesis. -/
theorem restartReduction_lwe {w : Y → ℚ} (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y) {n : ℕ}
    (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i))
    (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i))
    (Lf : ∀ i, ((Fin n → Digit 3) × (ι → Digit 3)) → (Fin (r i) → Y) → Prop)
    (Pre : ∀ i, (Fin (r i) → Y) → Prop)
    {g L : Fin k → ℝ} (hg : ∀ i, 0 < g i) (hL : ∀ i, 0 ≤ L i)
    (gap : ∀ i, 0 < L i ^ 2 - 1 - (3/2) * (d i : ℝ))
    (b : ∀ i, Fin (r i) → ι) (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2))
    {ε ℓ : ℝ} (hε0 : 0 ≤ ε) (hℓ0 : 0 ≤ ℓ)
    (hε : ∀ i, reductionError (N i) (d i) (g i) (L i) ≤ ε)
    (hℓ : ∀ i z, accept R g L Pre i z →
      (plantProb (plantWeight n cbdQ) (fun p ↦ Lf i p z) : ℝ) ≤ ℓ) :
    (failProb w (plantWeight n cbdQ) (accept R g L Pre) (decodeFail R (lwePlant σ b) Lf) b
        : ℝ) ≤
      (∏ i, (rejectProb w (accept R g L Pre) i : ℝ)) + ε + ℓ := by
  have hρ0 (p : (Fin n → Digit 3) × (ι → Digit 3)) : 0 ≤ plantWeight n cbdQ p := by
    unfold plantWeight
    exact mul_nonneg (Finset.prod_nonneg fun j _ ↦ cbdQ_nonneg _)
      (Finset.prod_nonneg fun j _ ↦ cbdQ_nonneg _)
  refine restartReduction hw hw0 (plantWeight_sum n cbdQ_sum) hρ0 R (lwePlant σ b)
    (fun i v ↦ lwePlant_marginal σ b i (fun a₁ a₂ h ↦ ?_) v) Lf Pre hg hL gap b hb hε0 hℓ0 hε hℓ
  have := hb (a₁ := ⟨i, a₁⟩) (a₂ := ⟨i, a₂⟩) h
  simpa using this

end SigabaNeo.Wall1.RestartReduction

#print axioms SigabaNeo.Wall1.RestartReduction.plantProb_not_unique
#print axioms SigabaNeo.Wall1.RestartReduction.reductionError_nonneg
#print axioms SigabaNeo.Wall1.RestartReduction.plantProb_decodeFail_le
#print axioms SigabaNeo.Wall1.RestartReduction.failProb_le_real
#print axioms SigabaNeo.Wall1.RestartReduction.restartReduction_avg
#print axioms SigabaNeo.Wall1.RestartReduction.restartReduction
#print axioms SigabaNeo.Wall1.RestartReduction.restartReduction_uniform
#print axioms SigabaNeo.Wall1.RestartReduction.restartReduction_single
#print axioms SigabaNeo.Wall1.RestartReduction.lwePlant_marginal
#print axioms SigabaNeo.Wall1.RestartReduction.restartReduction_lwe

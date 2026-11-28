module

public import Definitions.Def_LatticeAttack_Research_Wall1_BabaiLift
public import Definitions.Def_LatticeAttack_Research_Wall1_RestartReduction
public import Mathlib.Analysis.InnerProductSpace.PiL2
import all Definitions.Def_LatticeAttack_Research_Wall1_CBDTail
import all Definitions.Def_LatticeAttack_Research_Wall1_PlantBlindRestart
import all Definitions.Def_LatticeAttack_Research_Wall1_RestartReduction
import Mathlib.Tactic

set_option autoImplicit true

/-! # Discharging the lift hypothesis `hℓ` of `restartReduction` (PROOF_GAP Wall 1, Part 47)

`RestartReduction.restartReduction` takes the Babai-lift error as a hypothesis
`hℓ : ∀ i z, accept R g L Pre i z → Pr_p[Lf i p z] ≤ ℓ`. This file supplies a concrete lift event
`Lf` and prefix test `Pre` for which `hℓ` is a theorem.

Geometry (Part 47). Block `i` lives in `ℝ^{N i + 1}` (horizontal coordinates and height). The plant
vector is `u = (X, 1)` with `X = π i p` the block CBD(3) vector (`plantVec`). The plant-free reducer
supplies for every row block `z` a prefix `PrefixData`: basis vectors `b`, a Gram–Schmidt system
`bs` (`IsGSPair`) and horizontality `bs m (last) = 0`; the prefix has length `J i`.
* `Lf := liftFail`: Babai nearest-plane on the first `J i` prefix vectors fails to return `u` from
  *some* lift `u + Σ cₘ bₘ` (the strongest form; any concrete choice of lift fails less often).
* `Pre := prefixFloor`: the prefix floor test `gp i m ≤ ‖bs m‖` for `m < J i`.

Main results.
* `inner_plantVec`, `prefix_liftFail_le`: for a single horizontal prefix, the CBD(3) failure mass
  is `≤ Σ_{m<J} 2 exp(−gₘ²/12)`.
* `plantProb_liftFail_le`: the same for the plant law `ρ`, given the CBD(3) marginal `hπ`.
* `restartReduction_babai`: `restartReduction` with `hℓ` discharged:
  `Pr[fail] ≤ ∏ δᵢ + ε + ℓ` whenever `Σ_{m<J i} 2 exp(−(gp i m)²/12) ≤ ℓ` for every block.
* `restartReduction_lwe_babai`: the LWE-plant version (no marginal hypothesis). -/

public section

namespace SigabaNeo.Wall1.RestartLift

open SigabaNeo.Wall1 SigabaNeo.Wall1.MultiBlock SigabaNeo.Wall1.PlantBlindRestart
open SigabaNeo.Wall1.RestartReduction SigabaNeo.Wall1.BabaiLift
open SampleDeletion CBDTail Classical InnerProductSpace

/-! ## The plant vector and horizontal prefixes -/

/-- The plant vector `u = (X, 1) ∈ ℝ^{N+1}` for a CBD(3) vector `X` (centered coordinates). -/
noncomputable def plantVec {N : ℕ} (x : Fin N → Digit 3) : EuclideanSpace ℝ (Fin (N + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ ↦ ℝ) (fun c ↦ (centered (x c) : ℝ)) 1)

/-- Plant-free prefix data of a block: a basis prefix `b`, a Gram–Schmidt system `bs` for it, and
horizontality of the Gram–Schmidt vectors (they lie in the height-zero hyperplane). -/
structure PrefixData (N : ℕ) where
  b : ℕ → EuclideanSpace ℝ (Fin (N + 1))
  bs : ℕ → EuclideanSpace ℝ (Fin (N + 1))
  gs : IsGSPair b bs
  horiz : ∀ m, bs m (Fin.last N) = 0

/-- A horizontal basis (height-zero vectors, i.e. a basis of the null lattice `L₀`) together with
Mathlib's Gram–Schmidt process is prefix data. -/
noncomputable def PrefixData.ofGramSchmidt {N : ℕ} (b : ℕ → EuclideanSpace ℝ (Fin (N + 1)))
    (hb : ∀ m, b m (Fin.last N) = 0) : PrefixData N where
  b := b
  bs := gramSchmidt ℝ b
  gs := gramSchmidt_isGSPair b
  horiz m := by
    let f : EuclideanSpace ℝ (Fin (N + 1)) →ₗ[ℝ] ℝ :=
      (LinearMap.proj (Fin.last N)).comp (WithLp.linearEquiv 2 ℝ (Fin (N + 1) → ℝ)).toLinearMap
    have hspan : Submodule.span ℝ (b '' Set.Iic m) ≤ LinearMap.ker f := by
      rw [Submodule.span_le]
      rintro _ ⟨i, -, rfl⟩
      exact hb i
    exact hspan (gramSchmidt_mem_span ℝ b le_rfl)

theorem inner_plantVec {N : ℕ} (x : Fin N → Digit 3) (w : EuclideanSpace ℝ (Fin (N + 1)))
    (hw : w (Fin.last N) = 0) :
    inner ℝ (plantVec x) w = projection (fun c ↦ w c.castSucc) x := by
  rw [PiLp.inner_apply, Fin.sum_univ_castSucc]
  simp [plantVec, projection, hw, mul_comm]

theorem horizontal_sq_le {N : ℕ} (w : EuclideanSpace ℝ (Fin (N + 1))) :
    ∑ c : Fin N, w c.castSucc ^ 2 ≤ ‖w‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  linarith [sq_nonneg (w (Fin.last N))]

/-- **Lift failure for one horizontal prefix.** Under the prefix floor `0 ≤ gₘ ≤ ‖bs m‖`
(`m < J`), the CBD(3) probability that Babai fails to return `(X, 1)` from some lift is
`≤ Σ_{m<J} 2 exp(−gₘ²/12)`. -/
theorem prefix_liftFail_le {N : ℕ} (P : PrefixData N) (J : ℕ) (g : ℕ → ℝ)
    (hg0 : ∀ m < J, 0 ≤ g m) (hg : ∀ m < J, g m ≤ ‖P.bs m‖) :
    ∑ x with LiftFail P.b P.bs J (plantVec x), jointWeight x ≤
      ∑ m ∈ Finset.range J, 2 * Real.exp (-g m ^ 2 / 12) :=
  liftFail_le_floor P.gs J plantVec (fun m c ↦ P.bs m c.castSucc)
    (fun x m _ ↦ inner_plantVec x _ (P.horiz m)) (fun _ _ ↦ horizontal_sq_le _) g hg0 hg

/-! ## The restart instance -/

variable {Y ι P : Type*} [Fintype Y] [Fintype ι] [DecidableEq ι] [Fintype P] {k : ℕ}
  {r : Fin k → ℕ} {N d : Fin k → ℕ}

/-- The concrete lift event of block `i`: Babai on the first `J i` vectors of the plant-free
prefix `pre i z` fails to return `(π i p, 1)` from some lift. -/
@[expose] def liftFail (pre : ∀ i, (Fin (r i) → Y) → PrefixData (N i)) (J : Fin k → ℕ)
    (π : ∀ i, P → Fin (N i) → Digit 3) (i : Fin k) (p : P) (z : Fin (r i) → Y) : Prop :=
  LiftFail (pre i z).b (pre i z).bs (J i) (plantVec (π i p))

/-- The prefix floor test of block `i` (Part 47): `gp i m ≤ ‖b*_m‖` for every prefix index
`m < J i`. It depends on the rows only. -/
@[expose] def prefixFloor (pre : ∀ i, (Fin (r i) → Y) → PrefixData (N i)) (J : Fin k → ℕ)
    (gp : Fin k → ℕ → ℝ) (i : Fin k) (z : Fin (r i) → Y) : Prop :=
  ∀ m < J i, gp i m ≤ ‖(pre i z).bs m‖

omit [Fintype Y] [Fintype ι] [DecidableEq ι] in
/-- **The lift hypothesis, proved.** If the block-`i` plant has the product CBD(3) marginal and the
rows pass the prefix floor, the plant probability of lift failure is at most
`Σ_{m<J i} 2 exp(−(gp i m)²/12)`. -/
theorem plantProb_liftFail_le {ρ : P → ℚ} (pre : ∀ i, (Fin (r i) → Y) → PrefixData (N i))
    (J : Fin k → ℕ) (π : ∀ i, P → Fin (N i) → Digit 3) (gp : Fin k → ℕ → ℝ)
    (hgp : ∀ i m, 0 ≤ gp i m) (i : Fin k)
    (hπ : ∀ v, ((∑ p with π i p = v, ρ p : ℚ) : ℝ) = jointWeight v)
    {z : Fin (r i) → Y} (hz : prefixFloor pre J gp i z) :
    (plantProb ρ (fun p ↦ liftFail pre J π i p z) : ℝ) ≤
      ∑ m ∈ Finset.range (J i), 2 * Real.exp (-gp i m ^ 2 / 12) := by
  have fiber (f : (Fin (N i) → Digit 3) → ℝ) :
      ∑ p, (ρ p : ℝ) * f (π i p) = ∑ v, jointWeight v * f v := by
    rw [← Finset.sum_fiberwise Finset.univ (π i) (fun p ↦ (ρ p : ℝ) * f (π i p))]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [← hπ v, Rat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [(Finset.mem_filter.1 hp).2]
  have h := prefix_liftFail_le (pre i z) (J i) (gp i) (fun m _ ↦ hgp i m) hz
  unfold plantProb liftFail
  simp only [Rat.cast_sum, Rat.cast_mul, apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_one,
    Rat.cast_zero]
  rw [fiber (fun v ↦ if LiftFail (pre i z).b (pre i z).bs (J i) (plantVec v) then 1 else 0)]
  simpa [Finset.sum_filter] using h

/-- **Concrete restart reduction with the Babai lift proved.** `restartReduction` with the lift
event `liftFail` (Babai on the plant-free prefix of length `J i`) and the prefix floor test
`Pre := prefixFloor`. The hypothesis `hℓ` of `restartReduction` is replaced by the numerical
condition `Σ_{m<J i} 2 exp(−(gp i m)²/12) ≤ ℓ` (Part 47's `Σ 2 exp(−gₘ²/(4η))` at `η = 3`). -/
theorem restartReduction_babai {w : Y → ℚ} (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    {ρ : P → ℚ} (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p)
    (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i)) (π : ∀ i, P → Fin (N i) → Digit 3)
    (hπ : ∀ i v, ((∑ p with π i p = v, ρ p : ℚ) : ℝ) = jointWeight v)
    (pre : ∀ i, (Fin (r i) → Y) → PrefixData (N i)) (J : Fin k → ℕ) (gp : Fin k → ℕ → ℝ)
    (hgp : ∀ i m, 0 ≤ gp i m)
    {g L : Fin k → ℝ} (hg : ∀ i, 0 < g i) (hL : ∀ i, 0 ≤ L i)
    (gap : ∀ i, 0 < L i ^ 2 - 1 - (3/2) * (d i : ℝ))
    (b : ∀ i, Fin (r i) → ι) (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2))
    {ε ℓ : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ i, reductionError (N i) (d i) (g i) (L i) ≤ ε)
    (hℓ : ∀ i, ∑ m ∈ Finset.range (J i), 2 * Real.exp (-gp i m ^ 2 / 12) ≤ ℓ) (hℓ0 : 0 ≤ ℓ) :
    (failProb w ρ (accept R g L (prefixFloor pre J gp))
        (decodeFail R π (liftFail pre J π)) b : ℝ) ≤
      (∏ i, (rejectProb w (accept R g L (prefixFloor pre J gp)) i : ℝ)) + ε + ℓ :=
  restartReduction hw hw0 hρ hρ0 R π hπ (liftFail pre J π) (prefixFloor pre J gp) hg hL gap b hb
    hε0 hℓ0 hε fun i _ hz ↦
      (plantProb_liftFail_le pre J π gp hgp i (hπ i) hz.2).trans (hℓ i)

/-- **LWE instance with the Babai lift proved.** As `restartReduction_lwe`, with the lift event
`liftFail` against the block plant `(s, e restricted to block i)` and the prefix floor test; no
marginal or lift hypothesis remains. -/
theorem restartReduction_lwe_babai {w : Y → ℚ} (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    {n : ℕ} (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i))
    (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i))
    (pre : ∀ i, (Fin (r i) → Y) → PrefixData (N i)) (J : Fin k → ℕ) (gp : Fin k → ℕ → ℝ)
    (hgp : ∀ i m, 0 ≤ gp i m)
    {g L : Fin k → ℝ} (hg : ∀ i, 0 < g i) (hL : ∀ i, 0 ≤ L i)
    (gap : ∀ i, 0 < L i ^ 2 - 1 - (3/2) * (d i : ℝ))
    (b : ∀ i, Fin (r i) → ι) (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2))
    {ε ℓ : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ i, reductionError (N i) (d i) (g i) (L i) ≤ ε)
    (hℓ : ∀ i, ∑ m ∈ Finset.range (J i), 2 * Real.exp (-gp i m ^ 2 / 12) ≤ ℓ) (hℓ0 : 0 ≤ ℓ) :
    (failProb w (plantWeight n cbdQ) (accept R g L (prefixFloor pre J gp))
        (decodeFail R (lwePlant σ b) (liftFail pre J (lwePlant σ b))) b : ℝ) ≤
      (∏ i, (rejectProb w (accept R g L (prefixFloor pre J gp)) i : ℝ)) + ε + ℓ := by
  have hbi (i : Fin k) : Function.Injective (b i) := fun a₁ a₂ h ↦ by
    have := hb (a₁ := ⟨i, a₁⟩) (a₂ := ⟨i, a₂⟩) h
    simpa using this
  exact restartReduction_lwe hw hw0 σ R (liftFail pre J (lwePlant σ b)) (prefixFloor pre J gp)
    hg hL gap b hb hε0 hℓ0 hε fun i _ hz ↦
      (plantProb_liftFail_le pre J (lwePlant σ b) gp hgp i
        (lwePlant_marginal σ b i (hbi i)) hz.2).trans (hℓ i)

end SigabaNeo.Wall1.RestartLift

#print axioms SigabaNeo.Wall1.RestartLift.PrefixData.ofGramSchmidt
#print axioms SigabaNeo.Wall1.RestartLift.inner_plantVec
#print axioms SigabaNeo.Wall1.RestartLift.prefix_liftFail_le
#print axioms SigabaNeo.Wall1.RestartLift.plantProb_liftFail_le
#print axioms SigabaNeo.Wall1.RestartLift.restartReduction_babai
#print axioms SigabaNeo.Wall1.RestartLift.restartReduction_lwe_babai

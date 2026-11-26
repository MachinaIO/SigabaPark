module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

set_option autoImplicit true

public section

namespace SigabaNeo.Probability

open MeasureTheory ProbabilityTheory

/-- Give an incorrect vote score +1 and a correct vote score -1.
A strictly negative total then means a strict majority of correct votes.
The same bound holds for any scores in the interval with the indicated mean. -/
theorem iid_strict_majority {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (score : Ω → ℝ) (hm : Measurable score)
    (hb : ∀ x, score x ∈ Set.Icc (-1) 1) {γ : ℝ} (hγ : 0 ≤ γ)
    (hmean : ∫ x, score x ∂μ ≤ -2 * γ) (N : ℕ) :
    1 - Real.exp (-2 * N * γ ^ 2) ≤
      (Measure.pi (fun _ : Fin N ↦ μ)).real {x | ∑ i, score (x i) < 0} := by
  rcases Nat.eq_zero_or_pos N with rfl | hn
  · simp
  let P := Measure.pi (fun _ : Fin N ↦ μ)
  let X (i : Fin N) (x : Fin N → Ω) := score (x i)
  have hX (i : Fin N) : Measurable (X i) := hm.comp (measurable_pi_apply i)
  have hi : iIndepFun X P := iIndepFun_pi (fun _ ↦ hm.aemeasurable)
  have he (i : Fin N) : ∫ x, X i x ∂P ≤ -2 * γ := by
    dsimp only [X, P]
    rw [integral_comp_eval hm.aestronglyMeasurable]
    exact hmean
  let Y (i : Fin N) (x : Fin N → Ω) := X i x - ∫ z, X i z ∂P
  have hy : iIndepFun Y P :=
    hi.comp (fun i z ↦ z - ∫ x, X i x ∂P) (fun _ ↦ measurable_id.sub_const _)
  have hg (i : Fin N) : HasSubgaussianMGF (Y i) 1 P := by
    have hbi : ∀ᵐ x ∂P, X i x ∈ Set.Icc (-1) 1 := ae_of_all _ fun x ↦ hb (x i)
    convert hasSubgaussianMGF_of_mem_Icc (hX i).aemeasurable hbi using 1
    norm_num
  have hsum : ∑ i, (∫ x, X i x ∂P) ≤ N * (-2 * γ) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ he i)
  have h : P.real {x | 0 ≤ ∑ i, X i x} ≤ Real.exp (-(2 * N * γ)^2 / (2 * N)) := by
    apply le_trans (measureReal_mono (s₂ := {x | 2 * N * γ ≤ ∑ i, Y i x}) ?_)
    · simpa using HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hy
        (s := Finset.univ) (fun i _ ↦ hg i) (show 0 ≤ 2 * N * γ by positivity)
    · intro x hx
      change 0 ≤ ∑ i, X i x at hx
      change 2 * N * γ ≤ ∑ i, (X i x - _)
      rw [Finset.sum_sub_distrib]
      linarith
  have hc : (0 : ℝ) < N := by exact_mod_cast hn
  have hexp : -(2 * (N : ℝ) * γ)^2 / (2 * N) = -2 * N * γ^2 := by
    field_simp
    <;> ring
  rw [hexp] at h
  have hs : MeasurableSet {x | ∑ i, X i x < 0} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hcpl : {x | ∑ i, X i x < 0}ᶜ = {x | 0 ≤ ∑ i, X i x} := by
    ext x
    simp
  rw [← hcpl, measureReal_compl hs, probReal_univ] at h
  change 1 - _ ≤ P.real {x | ∑ i, X i x < 0}
  linarith

/-- Strict majority of successes for independent copies of a measurable event. -/
theorem iid_majority_count {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : Set Ω) (hA : MeasurableSet A)
    {γ : ℝ} (hγ : 0 ≤ γ) (hp : 1 / 2 + γ ≤ μ.real A) (N : ℕ) :
    1 - Real.exp (-2 * N * γ ^ 2) ≤ (Measure.pi (fun _ : Fin N ↦ μ)).real
      {x | N < 2 * ∑ i : Fin N, (A.indicator (fun _ ↦ 1 : Ω → ℕ) (x i))} := by
  classical
  let f := A.indicator (fun _ ↦ (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hA
  have hint : Integrable f μ := (integrable_const _).indicator hA
  have he : ∫ x, f x ∂μ = μ.real A := by simp [f, integral_indicator hA]
  apply le_trans (iid_strict_majority μ (fun x ↦ 1 - 2 * f x)
    (measurable_const.sub (measurable_const.mul hf)) _ hγ _ N)
  · apply measureReal_mono
    rotate_left
    · exact measure_ne_top _ _
    intro x hx
    change ∑ i, (1 - 2 * f (x i)) < 0 at hx
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hx
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at hx
    change N < 2 * ∑ i : Fin N, A.indicator _ (x i)
    have hcast (i : Fin N) : ((A.indicator (fun _ ↦ 1 : Ω → ℕ) (x i) : ℕ) : ℝ) =
        f (x i) := by by_cases ha : x i ∈ A <;> simp [f, ha]
    exact_mod_cast (show (N : ℝ) < 2 * ∑ i, ((A.indicator (fun _ ↦ 1 : Ω → ℕ)
      (x i) : ℕ) : ℝ) by simp_rw [hcast]; linarith)
  · intro x
    by_cases ha : x ∈ A <;> norm_num [f, ha, Set.mem_Icc]
  · rw [integral_sub (integrable_const _) (hint.const_mul _), integral_const_mul, he]
    simp
    linarith

/-- One tally operation per vote in addition to its individual generation cost. -/
theorem tally_cost {N : ℕ} (cost : Fin N → ℕ) (hc : ∀ i, cost i ≤ 5) :
    (∑ i, (cost i + 1)) ≤ 5 * N + N := by
  rw [Finset.sum_add_distrib]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hc i)
  simpa [Nat.mul_comm] using Nat.add_le_add_right h N

#print axioms iid_majority_count
#print axioms tally_cost
#print axioms iid_strict_majority

end SigabaNeo.Probability

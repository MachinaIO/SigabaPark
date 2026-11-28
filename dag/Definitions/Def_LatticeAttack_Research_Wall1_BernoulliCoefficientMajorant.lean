import Definitions.Def_LatticeAttack_Research_Wall1_FormalLogAdditivity

set_option autoImplicit true

/-! Coefficientwise absolute majorants for the Bernoulli factors in quartic defects. -/
noncomputable section
namespace SigabaNeo.Wall1.CoefficientMajorant
open PowerSeries Finset

def AbsMajorized (F H : PowerSeries ℝ) : Prop := ∀ n, |coeff n F| ≤ coeff n H

theorem AbsMajorized.nonneg {F H : PowerSeries ℝ} (h : AbsMajorized F H) (n : ℕ) :
    0 ≤ coeff n H := (abs_nonneg _).trans (h n)

theorem AbsMajorized.add {F G H K : PowerSeries ℝ}
    (hF : AbsMajorized F H) (hG : AbsMajorized G K) : AbsMajorized (F+G) (H+K) := by
  intro n
  simp only [map_add]
  exact (abs_add_le _ _).trans (add_le_add (hF n) (hG n))

theorem AbsMajorized.mul {F G H K : PowerSeries ℝ}
    (hF : AbsMajorized F H) (hG : AbsMajorized G K) : AbsMajorized (F*G) (H*K) := by
  intro n
  rw [coeff_mul, coeff_mul]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro ij _
  rw [abs_mul]
  exact mul_le_mul (hF ij.1) (hG ij.2) (abs_nonneg _) (hF.nonneg _)

theorem majorized_one : AbsMajorized (1 : PowerSeries ℝ) 1 := by
  intro n
  simp only [coeff_one]
  split_ifs <;> norm_num

theorem AbsMajorized.pow {F H : PowerSeries ℝ} (h : AbsMajorized F H) (m : ℕ) :
    AbsMajorized (F^m) (H^m) := by
  induction m with
  | zero => simpa using majorized_one
  | succ m ih => simpa only [pow_succ] using ih.mul h

theorem bernoulli (p ρ : ℝ) (hp : |p| ≤ ρ) :
    AbsMajorized (1+C p*X) (1+C ρ*X) := by
  intro n
  by_cases h0 : n = 0
  · subst n
    simp
  · by_cases h1 : n = 1
    · subst n
      simpa using hp
    · simp [coeff_one, coeff_C_mul, coeff_X, h0, h1]

theorem bernoulli_product {α : Type*} (S : Finset α) (p : α → ℝ) (ρ : ℝ)
    (hp : ∀ i ∈ S, |p i| ≤ ρ) :
    AbsMajorized (∏ i ∈ S, (1+C (p i)*X)) ((1+C ρ*X)^S.card) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using majorized_one
  | @insert a S ha ih =>
    rw [prod_insert ha, card_insert_of_notMem ha, pow_succ']
    exact (bernoulli (p a) ρ (hp a (mem_insert_self _ _))).mul
      (ih (fun i hi ↦ hp i (mem_insert_of_mem hi)))

/-- The squared four-input Bernoulli baseline has the eighth-power majorant. -/
theorem bernoulli_four_squared (p : Fin 4 → ℝ) (ρ : ℝ) (hp : ∀ i, |p i| ≤ ρ) :
    AbsMajorized ((∏ i : Fin 4, (1+C (p i)*X))^2) ((1+C ρ*X)^8) := by
  have h := (bernoulli_product univ p ρ (fun i _ ↦ hp i)).pow 2
  simpa only [card_univ, Fintype.card_fin, ← pow_mul] using h

/-- An absolute scalar mass bound persists after multiplication by a common majorant. -/
theorem weighted_mass {α : Type*} (S : Finset α) (e : α → ℝ)
    (F : α → PowerSeries ℝ) (H : PowerSeries ℝ) (D : ℝ)
    (hF : ∀ s ∈ S, AbsMajorized (F s) H) (hH : ∀ n, 0 ≤ coeff n H)
    (hmass : ∑ s ∈ S, |e s| ≤ D) (n : ℕ) :
    ∑ s ∈ S, |coeff n (C (e s) * F s)| ≤ D * coeff n H := by
  calc
    _ ≤ ∑ s ∈ S, |e s| * coeff n H := by
      apply sum_le_sum
      intro s hs
      rw [coeff_C_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hF s hs n) (abs_nonneg _)
    _ = (∑ s ∈ S, |e s|) * coeff n H := (sum_mul ..).symm
    _ ≤ D * coeff n H := mul_le_mul_of_nonneg_right hmass (hH n)

end SigabaNeo.Wall1.CoefficientMajorant
#print axioms SigabaNeo.Wall1.CoefficientMajorant.bernoulli_product
#print axioms SigabaNeo.Wall1.CoefficientMajorant.bernoulli_four_squared
#print axioms SigabaNeo.Wall1.CoefficientMajorant.weighted_mass

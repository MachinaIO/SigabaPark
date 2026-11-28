import Definitions.Def_LatticeAttack_Research_Wall1_FormalLogAdditivity
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit true

/-! All-order cancellation of mixed exact supports under a supplied series factorization. -/
noncomputable section
namespace SigabaNeo.Wall1.DisconnectedLogSupport
open Finset PowerSeries ExponentialCoefficientRecurrence
open scoped Classical
variable {α β : Type*}

lemma alternating_sum_zero (S : Finset α) (hS : S.Nonempty) :
    (∑ U ∈ S.powerset, (-1:ℝ)^U.card) = 0 := by
  exact_mod_cast sum_powerset_neg_one_pow_card_of_nonempty hS

/-- Functions of separate nonempty label sets have zero mixed alternating support sum. -/
theorem mixed_alternating_sum_zero (S : Finset α) (T : Finset β)
    (hS : S.Nonempty) (hT : T.Nonempty) (f : Finset α → ℝ) (g : Finset β → ℝ) :
    (∑ U ∈ S.powerset, ∑ V ∈ T.powerset,
      (-1:ℝ)^(U.card+V.card) * (f U+g V)) = 0 := by
  simp_rw [pow_add, mul_add]
  simp_rw [sum_add_distrib]
  have h1 : (∑ U ∈ S.powerset, ∑ V ∈ T.powerset,
      ((-1:ℝ)^U.card*(-1:ℝ)^V.card)*f U) = 0 := by
    apply sum_eq_zero
    intro U _
    calc
      _ = ((-1:ℝ)^U.card*f U) * ∑ V ∈ T.powerset, (-1:ℝ)^V.card := by
        rw [mul_sum]
        apply sum_congr rfl
        intro V _
        ring
      _ = 0 := by rw [alternating_sum_zero T hT, mul_zero]
  have h2 : (∑ U ∈ S.powerset, ∑ V ∈ T.powerset,
      ((-1:ℝ)^U.card*(-1:ℝ)^V.card)*g V) = 0 := by
    rw [sum_comm]
    apply sum_eq_zero
    intro V _
    calc
      _ = (∑ U ∈ S.powerset, (-1:ℝ)^U.card) * ((-1:ℝ)^V.card*g V) := by
        rw [sum_mul]
        apply sum_congr rfl
        intro U _
        ring
      _ = 0 := by rw [alternating_sum_zero S hS, zero_mul]
  rw [h1,h2,zero_add]

/-- A factorization for every pair of restricted label sets cancels mixed log supports
at every degree. Establishing that factorization for actual affine samples remains separate. -/
theorem mixed_log_coeff_zero (S : Finset α) (T : Finset β)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (F : Finset α → PowerSeries ℝ) (G : Finset β → PowerSeries ℝ)
    (H : Finset α → Finset β → PowerSeries ℝ)
    (hF : ∀ U ∈ S.powerset, constantCoeff (F U) = 1)
    (hG : ∀ V ∈ T.powerset, constantCoeff (G V) = 1)
    (hprod : ∀ U ∈ S.powerset, ∀ V ∈ T.powerset, H U V = F U * G V)
    (n : ℕ) :
    (∑ U ∈ S.powerset, ∑ V ∈ T.powerset,
      (-1:ℝ)^(U.card+V.card) * coeff n (logOf (H U V))) = 0 := by
  have he : (∑ U ∈ S.powerset, ∑ V ∈ T.powerset,
      (-1:ℝ)^(U.card+V.card) * coeff n (logOf (H U V))) =
      ∑ U ∈ S.powerset, ∑ V ∈ T.powerset, (-1:ℝ)^(U.card+V.card) *
        (coeff n (logOf (F U))+coeff n (logOf (G V))) := by
    apply sum_congr rfl
    intro U hU
    apply sum_congr rfl
    intro V hV
    rw [logOf_factorization_coeff (F U) (G V) (H U V) (hF U hU) (hG V hV)
      (hprod U hU V hV) n]
  rw [he]
  exact mixed_alternating_sum_zero S T hS hT _ _

lemma complement_sign (S U : Finset α) (hU : U ⊆ S) :
    (-1:ℝ)^(S.card-U.card) = (-1:ℝ)^S.card * (-1:ℝ)^U.card := by
  have hc := card_le_card hU
  symm
  calc
    _ = ((-1:ℝ)^(S.card-U.card) * (-1:ℝ)^U.card) * (-1:ℝ)^U.card := by
      have he : (-1:ℝ)^S.card = (-1:ℝ)^(S.card-U.card) * (-1:ℝ)^U.card := by
        rw [← pow_add, Nat.sub_add_cancel hc]
      exact congrArg (fun x : ℝ ↦ x * (-1:ℝ)^U.card) he
    _ = _ := by rw [mul_assoc, ← mul_pow]; norm_num

/-- Exact-support Mobius signs give the same all-degree cancellation. -/
theorem mixed_mobius_log_coeff_zero (S : Finset α) (T : Finset β)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (F : Finset α → PowerSeries ℝ) (G : Finset β → PowerSeries ℝ)
    (H : Finset α → Finset β → PowerSeries ℝ)
    (hF : ∀ U ∈ S.powerset, constantCoeff (F U) = 1)
    (hG : ∀ V ∈ T.powerset, constantCoeff (G V) = 1)
    (hprod : ∀ U ∈ S.powerset, ∀ V ∈ T.powerset, H U V = F U * G V)
    (n : ℕ) :
    (∑ U ∈ S.powerset, ∑ V ∈ T.powerset,
      (-1:ℝ)^((S.card-U.card)+(T.card-V.card)) * coeff n (logOf (H U V))) = 0 := by
  calc
    _ = (-1:ℝ)^(S.card+T.card) *
        ∑ U ∈ S.powerset, ∑ V ∈ T.powerset,
          (-1:ℝ)^(U.card+V.card) * coeff n (logOf (H U V)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro U hU
      rw [mul_sum]
      apply sum_congr rfl
      intro V hV
      rw [pow_add, complement_sign S U (mem_powerset.mp hU),
        complement_sign T V (mem_powerset.mp hV), pow_add, pow_add]
      ring
    _ = 0 := by rw [mixed_log_coeff_zero S T hS hT F G H hF hG hprod n, mul_zero]

/-- The same cancellation in the factorial-cumulant normalization used by the slack pipeline. -/
theorem mixed_factorialCumulant_zero (S : Finset α) (T : Finset β)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (F : Finset α → ℕ → ℝ) (G : Finset β → ℕ → ℝ)
    (H : Finset α → Finset β → ℕ → ℝ)
    (hF : ∀ U ∈ S.powerset, F U 0 = 1)
    (hG : ∀ V ∈ T.powerset, G V 0 = 1)
    (hprod : ∀ U ∈ S.powerset, ∀ V ∈ T.powerset,
      FactorialMomentTransfer.normalizedMomentSeries (H U V) =
        FactorialMomentTransfer.normalizedMomentSeries (F U) *
          FactorialMomentTransfer.normalizedMomentSeries (G V)) (n : ℕ) :
    (∑ U ∈ S.powerset, ∑ V ∈ T.powerset,
      (-1:ℝ)^((S.card-U.card)+(T.card-V.card)) *
        FactorialMomentTransfer.factorialCumulant (H U V) n) = 0 := by
  have h := mixed_mobius_log_coeff_zero S T hS hT
    (fun U ↦ FactorialMomentTransfer.normalizedMomentSeries (F U))
    (fun V ↦ FactorialMomentTransfer.normalizedMomentSeries (G V))
    (fun U V ↦ FactorialMomentTransfer.normalizedMomentSeries (H U V))
    (fun U hU ↦ by simpa only [FactorialMomentTransfer.constantCoeff_normalizedMomentSeries] using hF U hU)
    (fun V hV ↦ by simpa only [FactorialMomentTransfer.constantCoeff_normalizedMomentSeries] using hG V hV)
    hprod n
  calc
    _ = (n.factorial : ℝ) * (∑ U ∈ S.powerset, ∑ V ∈ T.powerset,
        (-1:ℝ)^((S.card-U.card)+(T.card-V.card)) *
          coeff n (logOf (FactorialMomentTransfer.normalizedMomentSeries (H U V)))) := by
      simp only [FactorialMomentTransfer.factorialCumulant, mul_sum]
      apply sum_congr rfl; intro U _
      apply sum_congr rfl; intro V _
      ring
    _ = 0 := by rw [h, mul_zero]

end SigabaNeo.Wall1.DisconnectedLogSupport
#print axioms SigabaNeo.Wall1.DisconnectedLogSupport.mixed_log_coeff_zero

#print axioms SigabaNeo.Wall1.DisconnectedLogSupport.mixed_mobius_log_coeff_zero

#print axioms SigabaNeo.Wall1.DisconnectedLogSupport.mixed_factorialCumulant_zero

import Definitions.Def_LatticeAttack_Research_Wall1_FormalCumulantBridge

set_option autoImplicit true

/-! Additivity of formal logarithms for normalized generating-series products. -/
noncomputable section
namespace SigabaNeo.Wall1.ExponentialCoefficientRecurrence
open PowerSeries

/-- A product factorization with constant terms one makes the formal logarithm additive. -/
theorem logOf_mul_normalized (f g : PowerSeries ℝ)
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    logOf (f*g) = logOf f + logOf g := by
  have hfg : constantCoeff (f*g) = 1 := by simp [hf,hg]
  have hne : f*g ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hfg
    norm_num at hfg
  apply derivative.ext
  · apply mul_right_cancel₀ hne
    rw [derivative_logOf_mul _ hfg, map_add, Derivation.leibniz, smul_eq_mul]
    have hdf := derivative_logOf_mul f hf
    have hdg := derivative_logOf_mul g hg
    calc
      _ = (derivative (logOf f)*f)*g + (derivative (logOf g)*g)*f := by rw [hdf,hdg]; ring
      _ = _ := by ring
  · simp [constantCoeff_logOf hf, constantCoeff_logOf hg, constantCoeff_logOf hfg]

/-- A supplied exact generating-series factorization implies coefficientwise cumulant additivity.
No factorization or probabilistic independence is inferred by this theorem. -/
theorem logOf_factorization_coeff (f g h : PowerSeries ℝ)
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (hh : h = f*g) (n : ℕ) :
    coeff n (logOf h) = coeff n (logOf f) + coeff n (logOf g) := by
  rw [hh, logOf_mul_normalized f g hf hg, map_add]

end SigabaNeo.Wall1.ExponentialCoefficientRecurrence

namespace SigabaNeo.Wall1.FactorialMomentTransfer
open PowerSeries ExponentialCoefficientRecurrence

/-- Additivity of factorial cumulants under an exact normalized moment-series product. -/
theorem factorialCumulant_add_of_product (F G H : ℕ → ℝ)
    (hF : F 0 = 1) (hG : G 0 = 1)
    (hprod : normalizedMomentSeries H = normalizedMomentSeries F * normalizedMomentSeries G)
    (n : ℕ) : factorialCumulant H n = factorialCumulant F n + factorialCumulant G n := by
  unfold factorialCumulant
  rw [logOf_factorization_coeff _ _ _
    (by rw [constantCoeff_normalizedMomentSeries,hF])
    (by rw [constantCoeff_normalizedMomentSeries,hG]) hprod n, mul_add]

end SigabaNeo.Wall1.FactorialMomentTransfer
#print axioms SigabaNeo.Wall1.ExponentialCoefficientRecurrence.logOf_mul_normalized
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.factorialCumulant_add_of_product

import Definitions.Def_LatticeAttack_Research_Wall1_FormalLogAdditivity

set_option autoImplicit true

/-! A denominator-cleared recurrence preserving four-input triple corrections. -/
noncomputable section
namespace SigabaNeo.Wall1.FourLogRecurrence
open PowerSeries ExponentialCoefficientRecurrence

def correction (F B G₁ G₂ G₃ G₄ : PowerSeries ℝ) : PowerSeries ℝ :=
  logOf F + 2 * logOf B - (logOf G₁ + logOf G₂ + logOf G₃ + logOf G₄)

/-- Each singleton appears in three triple baselines, leaving twice the full baseline log. -/
theorem correction_eq_subtract_proper
    (F A B C D G₁ G₂ G₃ G₄ : PowerSeries ℝ)
    (ha : constantCoeff A = 1) (hb : constantCoeff B = 1)
    (hc : constantCoeff C = 1) (hd : constantCoeff D = 1) :
    correction F (A*B*C*D) G₁ G₂ G₃ G₄ =
      logOf F - (logOf A + logOf B + logOf C + logOf D) -
      ((logOf G₁ - (logOf A + logOf B + logOf C)) +
       (logOf G₂ - (logOf A + logOf B + logOf D)) +
       (logOf G₃ - (logOf A + logOf C + logOf D)) +
       (logOf G₄ - (logOf B + logOf C + logOf D))) := by
  unfold correction
  rw [logOf_mul_normalized (A*B*C) D (by simp [ha, hb, hc]) hd,
    logOf_mul_normalized (A*B) C (by simp [ha, hb]) hc,
    logOf_mul_normalized A B ha hb]
  ring

def denominator (F B G₁ G₂ G₃ G₄ : PowerSeries ℝ) : PowerSeries ℝ :=
  F * B * G₁ * G₂ * G₃ * G₄

def source (F B G₁ G₂ G₃ G₄ : PowerSeries ℝ) : PowerSeries ℝ :=
  derivative F * B * G₁ * G₂ * G₃ * G₄ +
    2 * derivative B * F * G₁ * G₂ * G₃ * G₄ -
    (derivative G₁ * F * B * G₂ * G₃ * G₄ +
      derivative G₂ * F * B * G₁ * G₃ * G₄ +
      derivative G₃ * F * B * G₁ * G₂ * G₄ +
      derivative G₄ * F * B * G₁ * G₂ * G₃)

theorem correction_derivative_identity (F B G₁ G₂ G₃ G₄ : PowerSeries ℝ)
    (hF : constantCoeff F = 1) (hB : constantCoeff B = 1)
    (h₁ : constantCoeff G₁ = 1) (h₂ : constantCoeff G₂ = 1)
    (h₃ : constantCoeff G₃ = 1) (h₄ : constantCoeff G₄ = 1) :
    derivative (correction F B G₁ G₂ G₃ G₄) * denominator F B G₁ G₂ G₃ G₄ =
      source F B G₁ G₂ G₃ G₄ := by
  have hf := derivative_logOf_mul F hF
  have hb := derivative_logOf_mul B hB
  have h1 := derivative_logOf_mul G₁ h₁
  have h2 := derivative_logOf_mul G₂ h₂
  have h3 := derivative_logOf_mul G₃ h₃
  have h4 := derivative_logOf_mul G₄ h₄
  have htwo : derivative (2 : PowerSeries ℝ) = 0 := by
    simpa using (derivative (R := ℝ)).map_natCast 2
  unfold correction denominator source
  simp only [map_sub, map_add, Derivation.leibniz, htwo, mul_zero, add_zero,
    smul_eq_mul]
  calc
    _ = (derivative (logOf F) * F) * B * G₁ * G₂ * G₃ * G₄ +
      2 * (derivative (logOf B) * B) * F * G₁ * G₂ * G₃ * G₄ -
      ((derivative (logOf G₁) * G₁) * F * B * G₂ * G₃ * G₄ +
       (derivative (logOf G₂) * G₂) * F * B * G₁ * G₃ * G₄ +
       (derivative (logOf G₃) * G₃) * F * B * G₁ * G₂ * G₄ +
       (derivative (logOf G₄) * G₄) * F * B * G₁ * G₂ * G₃) := by ring
    _ = _ := by rw [hf, hb, h1, h2, h3, h4]

theorem correction_coefficient_recurrence (F B G₁ G₂ G₃ G₄ : PowerSeries ℝ)
    (hF : constantCoeff F = 1) (hB : constantCoeff B = 1)
    (h₁ : constantCoeff G₁ = 1) (h₂ : constantCoeff G₂ = 1)
    (h₃ : constantCoeff G₃ = 1) (h₄ : constantCoeff G₄ = 1) (n : ℕ) :
    (n+1 : ℝ) * coeff (n+1) (correction F B G₁ G₂ G₃ G₄) =
      coeff n (source F B G₁ G₂ G₃ G₄) -
      ∑ i ∈ Finset.range n,
        ((i+1 : ℝ) * coeff (i+1) (correction F B G₁ G₂ G₃ G₄)) *
          coeff (n-i) (denominator F B G₁ G₂ G₃ G₄) := by
  have hd : constantCoeff (denominator F B G₁ G₂ G₃ G₄) = 1 := by
    simp only [denominator, map_mul, hF, hB, h₁, h₂, h₃, h₄, one_mul]
  have h := congrArg (coeff n)
    (correction_derivative_identity F B G₁ G₂ G₃ G₄ hF hB h₁ h₂ h₃ h₄)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] at h
  simp only [coeff_derivative, Nat.sub_self, coeff_zero_eq_constantCoeff_apply,
    hd, mul_one] at h
  simp_rw [mul_comm (coeff _ (correction F B G₁ G₂ G₃ G₄))] at h
  linarith

end SigabaNeo.Wall1.FourLogRecurrence
#print axioms SigabaNeo.Wall1.FourLogRecurrence.correction_coefficient_recurrence

#print axioms SigabaNeo.Wall1.FourLogRecurrence.correction_eq_subtract_proper

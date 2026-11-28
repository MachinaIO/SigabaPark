import Definitions.Def_LatticeAttack_Research_Wall1_CanonicalFactorialCorrection

set_option autoImplicit true

/-! # Canonical corrections in ordinary coefficient normalization

Dividing the factorial-moment convolution by h! gives the coefficient product
with mu^j/j!. These finite identities do not assume a logarithm or exponential
representation of the moment sequence.
-/

noncomputable section
namespace SigabaNeo.Wall1.FactorialMomentTransfer
open Finset

theorem transferCoefficient_div_factorial (μ : ℝ) {h k : ℕ} (hk : k ≤ h) :
    transferCoefficient μ h k / (h.factorial : ℝ) =
      μ^(h-k) / ((h-k).factorial : ℝ) := by
  have hf : (h.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero h
  simp only [transferCoefficient, ite_eq_left hk]
  field_simp

/-- Ordinary coefficient convolution obtained from the exact factorial-moment identity. -/
theorem normalized_convolution (F : ℕ → ℝ) (μ : ℝ) (h : ℕ) :
    F h / (h.factorial : ℝ) =
      ∑ k ∈ range (h+1), canonicalCorrection F μ k *
        (μ^(h-k) / ((h-k).factorial : ℝ)) := by
  rw [canonical_convolution F μ h, sum_div]
  apply sum_congr rfl
  intro k hk
  rw [mul_div_assoc, transferCoefficient_div_factorial μ (by have := mem_range.mp hk; omega)]

/-- Any ordinary coefficient sequence with this normalized convolution is canonical
through the stated finite degree. No sign or normalization hypothesis on F is needed. -/
theorem normalized_convolution_unique (F d : ℕ → ℝ) (μ : ℝ) (N : ℕ)
    (hd : ∀ h, h ≤ N → F h / (h.factorial : ℝ) =
      ∑ k ∈ range (h+1), d k * (μ^(h-k) / ((h-k).factorial : ℝ))) :
    ∀ h, h ≤ N → d h = canonicalCorrection F μ h := by
  apply canonicalCorrection_unique F d μ N
  intro h hh
  have hf : (h.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero h
  have he := congrArg (fun x : ℝ ↦ x * (h.factorial : ℝ)) (hd h hh)
  rw [div_mul_cancel₀ _ hf, sum_mul] at he
  rw [he]
  apply sum_congr rfl
  intro k hk
  have hkh : k ≤ h := by have := mem_range.mp hk; omega
  simp only [transferCoefficient, ite_eq_left hkh]
  ring

end SigabaNeo.Wall1.FactorialMomentTransfer

#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.transferCoefficient_div_factorial
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.normalized_convolution
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.normalized_convolution_unique

import Definitions.Def_LatticeAttack_Research_Wall1_FactorialMomentTransfer

set_option autoImplicit true

/-! # Canonical finite factorial corrections

Triangular inversion supplies the convolution identities for every moment
sequence. The size of these corrections remains a separate quantitative claim.
-/

noncomputable section
namespace SigabaNeo.Wall1.FactorialMomentTransfer
open Finset

def canonicalCorrection (F : ℕ → ℝ) (μ : ℝ) (n : ℕ) : ℝ :=
  (F n - ∑ k : Fin n, canonicalCorrection F μ k * transferCoefficient μ n k) /
    (n.factorial : ℝ)
termination_by n

theorem canonicalCorrection_eq (F : ℕ → ℝ) (μ : ℝ) (n : ℕ) :
    canonicalCorrection F μ n =
      (F n - ∑ k ∈ range n, canonicalCorrection F μ k * transferCoefficient μ n k) /
        (n.factorial : ℝ) := by
  rw [canonicalCorrection]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ canonicalCorrection F μ k * transferCoefficient μ n k) n]

theorem canonicalCorrection_zero (F : ℕ → ℝ) (μ : ℝ) :
    canonicalCorrection F μ 0 = F 0 := by
  rw [canonicalCorrection_eq]
  simp

theorem canonicalCorrection_one (F : ℕ → ℝ) (μ : ℝ) :
    canonicalCorrection F μ 1 = F 1 - F 0 * μ := by
  rw [canonicalCorrection_eq]
  simp [canonicalCorrection_zero, transferCoefficient]

theorem canonical_convolution (F : ℕ → ℝ) (μ : ℝ) (h : ℕ) :
    F h = ∑ k ∈ range (h+1), canonicalCorrection F μ k * transferCoefficient μ h k := by
  rw [sum_range_succ]
  have hfac : (h.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero h
  have hdiag : transferCoefficient μ h h = (h.factorial : ℝ) := by
    simp [transferCoefficient]
  rw [hdiag, canonicalCorrection_eq F μ h]
  field_simp
  ring

theorem canonical_convolution_range (F : ℕ → ℝ) (μ : ℝ) {h N : ℕ} (hh : h ≤ N) :
    F h = ∑ k ∈ range (N+1), canonicalCorrection F μ k * transferCoefficient μ h k := by
  rw [canonical_convolution F μ h]
  apply sum_subset (range_mono (Nat.add_le_add_right hh 1))
  intro k hkN hkh
  have hhk : ¬ k ≤ h := by simpa using hkh
  simp [transferCoefficient, hhk]

/-- Any other coefficient sequence with the same finite convolution agrees with
the canonical one. This is the bridge for separately constructed series coefficients. -/
theorem canonicalCorrection_unique (F d : ℕ → ℝ) (μ : ℝ) (N : ℕ)
    (hd : ∀ h, h ≤ N → F h =
      ∑ k ∈ range (h+1), d k * transferCoefficient μ h k) :
    ∀ h, h ≤ N → d h = canonicalCorrection F μ h := by
  intro h
  induction h using Nat.strong_induction_on with
  | ind h ih =>
    intro hh
    have he := hd h hh
    have hc := canonical_convolution F μ h
    rw [sum_range_succ] at he hc
    have hs : (∑ k ∈ range h, d k * transferCoefficient μ h k) =
        ∑ k ∈ range h, canonicalCorrection F μ k * transferCoefficient μ h k := by
      apply sum_congr rfl
      intro k hk
      rw [ih k (mem_range.mp hk) (by have := mem_range.mp hk; omega)]
    rw [hs] at he
    have hdiag : transferCoefficient μ h h ≠ 0 := by
      simp [transferCoefficient, Nat.factorial_ne_zero]
    exact mul_right_cancel₀ hdiag (by linarith [he, hc])

/-- The reference factorial moments mu^h have no positive-order corrections.
This algebraic statement makes no assertion about the actual count distribution. -/
theorem canonicalCorrection_reference (μ : ℝ) (n : ℕ) :
    canonicalCorrection (fun h ↦ μ^h) μ n = if n = 0 then 1 else 0 := by
  symm
  apply canonicalCorrection_unique (fun h ↦ μ^h) (fun k ↦ if k = 0 then 1 else 0) μ n
    (fun h hh ↦ ?_) n le_rfl
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range, Nat.zero_lt_succ, ite_true]
  simp [transferCoefficient, Nat.factorial_ne_zero]

end SigabaNeo.Wall1.FactorialMomentTransfer
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.canonical_convolution_range
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.canonicalCorrection_zero
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.canonicalCorrection_one
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.canonicalCorrection_unique
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.canonicalCorrection_reference

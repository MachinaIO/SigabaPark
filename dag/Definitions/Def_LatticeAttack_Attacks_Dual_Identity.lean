import Definitions.Def_LatticeAttack_Attacks_Dual
import Mathlib.Tactic.FieldSimp

set_option autoImplicit true

/-! For the one-dimensional identity matrix the modular dual kernel is qℤ.
The cosine score is constant for every possible list from this lattice. -/

namespace SigabaNeo.DualMoments

/-- Every list of multiples of the modulus evaluates to its length on every input. -/
theorem identityKernel_score {q : ℤ} (hq : q ≠ 0) {N : ℕ} (w : Fin N → ℤ)
    (hw : ∀ i, q ∣ w i) (b : ℤ) :
    score (fun i (x : ℤ) ↦ 2 * Real.pi * (w i : ℝ) * x / q) b = N := by
  have term (i : Fin N) : Real.cos (2 * Real.pi * (w i : ℝ) * b / q) = 1 := by
    obtain ⟨k, hk⟩ := hw i
    rw [hk]
    convert Real.cos_int_mul_two_pi (k * b) using 1
    push_cast
    congr 1
    field_simp
  simp [score, term]

/-- This includes the uniform law on a complete set of residue representatives. -/
theorem identityKernel_mean {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∑ x, p x = 1) (b : Ω → ℤ) {q : ℤ} (hq : q ≠ 0) {N : ℕ}
    (w : Fin N → ℤ) (hw : ∀ i, q ∣ w i) :
    moment p (fun x ↦ score (fun i (y : ℤ) ↦ 2 * Real.pi * (w i : ℝ) * y / q) (b x)) = N := by
  simp only [identityKernel_score hq w hw, moment, ← Finset.sum_mul, hp, one_mul]

end SigabaNeo.DualMoments

#print axioms SigabaNeo.DualMoments.identityKernel_score
#print axioms SigabaNeo.DualMoments.identityKernel_mean

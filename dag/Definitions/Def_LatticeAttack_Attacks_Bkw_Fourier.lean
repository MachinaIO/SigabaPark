module

public import Mathlib.Analysis.Complex.Basic

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.Attacks.Bkw

open ComplexConjugate

/-- Expectation with fresh independent children at each difference node. The base weights
may be any real weights; probability weights give the usual expectation. -/
noncomputable def errorMean {ι G : Type*} [Fintype ι] [Sub G] (p : ι → ℝ) (e : ι → G) :
    ℕ → (G → ℂ) → ℂ
  | 0, f => ∑ i, (p i : ℂ) * f (e i)
  | a + 1, f => errorMean p e a fun x ↦ errorMean p e a fun y ↦ f (x - y)

private theorem mean_mul {ι G : Type*} [Fintype ι] [Sub G] (p : ι → ℝ) (e : ι → G)
    (a : ℕ) (c : ℂ) (f : G → ℂ) :
    errorMean p e a (fun x ↦ c * f x) = c * errorMean p e a f := by
  induction a generalizing f with
  | zero => simp [errorMean, Finset.mul_sum, mul_left_comm]
  | succ a ih => simp only [errorMean, ih]

private theorem mean_conj {ι G : Type*} [Fintype ι] [Sub G] (p : ι → ℝ) (e : ι → G)
    (a : ℕ) (f : G → ℂ) :
    errorMean p e a (fun x ↦ conj (f x)) = conj (errorMean p e a f) := by
  induction a generalizing f with
  | zero => simp [errorMean]
  | succ a ih => simp only [errorMean, ih]

/-- Exact magnitude for a character evaluated on a balanced tree of independent differences. -/
theorem errorMean_norm {ι G : Type*} [Fintype ι] [Sub G] (p : ι → ℝ) (e : ι → G)
    (ψ : G → ℂ) (hψ : ∀ x y, ψ (x - y) = ψ x * conj (ψ y)) (a : ℕ) :
    ‖errorMean p e a ψ‖ = ‖∑ i, (p i : ℂ) * ψ (e i)‖ ^ (2 ^ a) := by
  induction a with
  | zero => simp [errorMean]
  | succ a ih =>
    simp only [errorMean, hψ, mean_mul, mean_conj]
    simp_rw [mul_comm (ψ _)]
    rw [mean_mul, norm_mul, Complex.norm_conj, ih, pow_succ 2, pow_mul, pow_two]

#print axioms errorMean_norm

end SigabaNeo.Lattices.Attacks.Bkw

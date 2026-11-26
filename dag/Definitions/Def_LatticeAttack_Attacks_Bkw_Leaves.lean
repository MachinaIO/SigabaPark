module

public import Definitions.Def_LatticeAttack_Attacks_Bkw_Fresh
import all Definitions.Def_LatticeAttack_Attacks_Bkw_Fourier

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.Attacks.Bkw

/-- Assignments of independently drawn leaves to a complete binary tree. -/
@[expose] def LeafDraw (ι : Type*) : ℕ → Type _
  | 0 => ι
  | a + 1 => LeafDraw ι a × LeafDraw ι a

noncomputable instance {ι : Type*} [Fintype ι] (a : ℕ) : Fintype (LeafDraw ι a) := by
  induction a with
  | zero => exact inferInstanceAs (Fintype ι)
  | succ a ih => exact inferInstanceAs (Fintype (LeafDraw ι a × LeafDraw ι a))

def leafWeight {ι : Type*} (p : ι → ℝ) : (a : ℕ) → LeafDraw ι a → ℝ
  | 0, i => p i
  | a + 1, (l, r) => leafWeight p a l * leafWeight p a r

def leafDifference {ι G : Type*} [Sub G] (e : ι → G) : (a : ℕ) → LeafDraw ι a → G
  | 0, i => e i
  | a + 1, (l, r) => leafDifference e a l - leafDifference e a r

/-- Expand the recursive expectation against the product weights of all leaf assignments. -/
theorem errorMean_leaves {ι G : Type*} [Fintype ι] [Sub G] (p : ι → ℝ) (e : ι → G)
    (a : ℕ) (f : G → ℂ) :
    errorMean p e a f = ∑ x, (leafWeight p a x : ℂ) * f (leafDifference e a x) := by
  induction a generalizing f with
  | zero => rfl
  | succ a ih =>
    simp only [errorMean, ih]
    change _ = ∑ x : LeafDraw ι a × LeafDraw ι a, _
    rw [Fintype.sum_prod_type]
    simp only [Finset.mul_sum, leafWeight, leafDifference, Complex.ofReal_mul, mul_assoc]

open ComplexConjugate

/-- At every positive depth the character mean itself equals the indicated real power. -/
theorem errorMean_succ {ι G : Type*} [Fintype ι] [Sub G] (p : ι → ℝ) (e : ι → G)
    (ψ : G → ℂ) (hψ : ∀ x y, ψ (x - y) = ψ x * conj (ψ y)) (a : ℕ) :
    errorMean p e (a + 1) ψ = ((‖∑ i, (p i : ℂ) * ψ (e i)‖ ^ (2 ^ (a + 1)) : ℝ) : ℂ) := by
  simp only [errorMean, hψ, mean_mul, mean_conj]
  simp_rw [mul_comm (ψ _)]
  rw [mean_mul, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    errorMean_norm p e ψ hψ a, pow_succ 2, pow_mul]

#print axioms errorMean_succ
#print axioms errorMean_leaves

end SigabaNeo.Lattices.Attacks.Bkw

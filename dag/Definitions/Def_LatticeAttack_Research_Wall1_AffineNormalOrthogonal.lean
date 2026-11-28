import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit true

/-! Explicit triangular orthogonal witnesses for a three-dimensional affine-relation lattice. -/
noncomputable section
namespace SigabaNeo.Wall1.AffineNormalOrthogonal
open InnerProductSpace

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- A Euclidean vector with three specified coordinates. -/
def vec (x y z : ℝ) : Space := WithLp.toLp 2 ![x, y, z]

/-- Squared length of the normal to the two homogeneous generators. -/
def discriminant (u v : ℝ) : ℝ := u^2 + v^2 + (u+v)^2

/-- The integer-lattice generators, with real parameters for the algebraic identities. -/
def generators (u v a b q : ℝ) : Fin 3 → Space :=
  ![vec 1 1 1, vec v (-u) 0, q • vec a b 0]

/-- Orthogonal witnesses in the same triangular order as the generators. -/
def witnesses (u v q : ℝ) : Fin 3 → Space :=
  ![vec 1 1 1, vec v (-u) 0 - ((v-u)/3) • vec 1 1 1,
    (q / discriminant u v) • vec u v (-u-v)]

/-- The exact squared Gram--Schmidt lengths of these witnesses. -/
def squaredLengths (u v q : ℝ) : Fin 3 → ℝ :=
  ![3, discriminant u v / 3, q^2 / discriminant u v]

lemma inner_vec (x y z a b c : ℝ) :
    ⟪vec x y z, vec a b c⟫_ℝ = x*a + y*b + z*c := by
  simp [vec, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

/-- The witnesses have the exact desired norm profile. -/
theorem witnesses_norm_sq (u v q : ℝ) (hD : 0 < discriminant u v) (i : Fin 3) :
    ‖witnesses u v q i‖^2 = squaredLengths u v q i := by
  have hD0 := ne_of_gt hD
  fin_cases i <;>
    simp [witnesses, squaredLengths, EuclideanSpace.real_norm_sq_eq, vec, Fin.sum_univ_succ]
  · norm_num
  · unfold discriminant
    ring
  · field_simp
    unfold discriminant
    ring

/-- Each diagonal pairing equals the corresponding squared witness length. -/
theorem witnesses_diagonal (u v a b q : ℝ) (hbez : u*a + v*b = 1)
    (hD : 0 < discriminant u v) (i : Fin 3) :
    ⟪witnesses u v q i, generators u v a b q i⟫_ℝ = ‖witnesses u v q i‖^2 := by
  rw [witnesses_norm_sq u v q hD]
  fin_cases i <;>
    simp [witnesses, generators, squaredLengths, vec, PiLp.inner_apply,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  · norm_num
  · unfold discriminant
    ring
  · have hD0 := ne_of_gt hD
    field_simp
    linear_combination q^2 * hbez

/-- A later witness is orthogonal to every earlier generator. -/
theorem witnesses_lower_orthogonal (u v a b q : ℝ) (i j : Fin 3) (hij : i < j) :
    ⟪witnesses u v q j, generators u v a b q i⟫_ℝ = 0 := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    simp [witnesses, generators, vec, PiLp.inner_apply, Fin.sum_univ_succ]
    ring

/-- Positive modulus and discriminant make all witness norms strictly positive. -/
theorem witnesses_norm_pos (u v q : ℝ) (hq : 0 < q) (hD : 0 < discriminant u v)
    (i : Fin 3) : 0 < ‖witnesses u v q i‖ := by
  have hs : 0 < ‖witnesses u v q i‖^2 := by
    rw [witnesses_norm_sq u v q hD]
    fin_cases i <;> simp [squaredLengths] <;> positivity
  nlinarith [norm_nonneg (witnesses u v q i)]

end SigabaNeo.Wall1.AffineNormalOrthogonal
#print axioms SigabaNeo.Wall1.AffineNormalOrthogonal.witnesses_norm_sq
#print axioms SigabaNeo.Wall1.AffineNormalOrthogonal.witnesses_diagonal
#print axioms SigabaNeo.Wall1.AffineNormalOrthogonal.witnesses_lower_orthogonal
#print axioms SigabaNeo.Wall1.AffineNormalOrthogonal.witnesses_norm_pos

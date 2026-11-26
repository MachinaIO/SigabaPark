import SigabaNeoStd.Lattices.Algorithms.Gauss
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.Order.Antidiag.Finsupp

set_option autoImplicit true

namespace SigabaNeo.Lattices.AroraGe

/-- Exponents of all monomials through degree T, including the constant. -/
noncomputable def xlExponents (n T : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finset.range (T + 1)).biUnion (Finset.univ.finsuppAntidiag ·)

variable {K : Type*} [Field K] {m n : ℕ}

/-- Coefficient matrix for the multiples of the input polynomials by monomials
through degree T-d. For inputs of degree at most d ≤ T the columns cover each product. -/
noncomputable def macaulayMatrix (f : Fin m → MvPolynomial (Fin n) K) (d T : ℕ) :
    Matrix (Fin (m * (xlExponents n (T - d)).card)) (Fin (xlExponents n T).card) K := by
  classical
  let rows := Fintype.equivFinOfCardEq (α := Fin m × ↥(xlExponents n (T - d)))
    (n := m * (xlExponents n (T - d)).card) (by simp)
  let cols := Fintype.equivFinOfCardEq (α := ↥(xlExponents n T))
    (n := (xlExponents n T).card) (by simp)
  exact Matrix.of fun i j ↦
    let r := rows.symm i
    (MvPolynomial.monomial r.2.val 1 * f r.1).coeff (cols.symm j).val

theorem macaulay_fieldOps_le [DecidableEq K] (f : Fin m → MvPolynomial (Fin n) K) (d T : ℕ)
    (c : Fin (m * (xlExponents n (T - d)).card) → K) :
    (SigabaNeo.Gauss.solve (macaulayMatrix f d T) c).2 ≤
      5 * (m * (xlExponents n (T - d)).card) * (xlExponents n T).card *
        ((xlExponents n T).card + 1) :=
  SigabaNeo.Gauss.fieldOps_le _ _

#print axioms macaulay_fieldOps_le

end SigabaNeo.Lattices.AroraGe

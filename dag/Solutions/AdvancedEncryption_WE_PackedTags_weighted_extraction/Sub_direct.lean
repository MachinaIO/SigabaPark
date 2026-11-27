import Mathlib
import CslibFrontier.Foundations.Algebra.Negacyclic
/-- Weighted extracted rows of repeated negacyclic samples recover the packed messages and noise. -/
theorem solution {R ι : Type*} [CommRing R] [Fintype ι] {n : ℕ}
    (a : ι → Fin n → R) (j : ι → Fin n) (sk : Fin n → R) (w m e : ι → R) :
    (∑ i, w i * (Cslib.negacyclicMul (a i) sk (j i) + m i + e i))
      - (∑ t, (∑ i, w i * Cslib.rotMatrix (a i) (j i) t) * sk t) =
    ∑ i, w i * m i + ∑ i, w i * e i := by
  simp only [Cslib.negacyclicMul, Matrix.mulVec, dotProduct, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset ι))]
  abel

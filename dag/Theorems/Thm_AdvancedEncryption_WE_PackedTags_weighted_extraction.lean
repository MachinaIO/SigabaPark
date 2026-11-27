import Mathlib
import CslibFrontier.Foundations.Algebra.Negacyclic
/-- Weighted extracted rows of repeated negacyclic samples recover the packed messages and noise. -/
theorem AdvancedEncryption.WE.PackedTags.weighted_extraction {R ι : Type*} [CommRing R] [Fintype ι] {n : ℕ}
    (a : ι → Fin n → R) (j : ι → Fin n) (sk : Fin n → R) (w m e : ι → R) :
    (∑ i, w i * (Cslib.negacyclicMul (a i) sk (j i) + m i + e i))
      - (∑ t, (∑ i, w i * Cslib.rotMatrix (a i) (j i) t) * sk t) =
    ∑ i, w i * m i + ∑ i, w i * e i := by sorry

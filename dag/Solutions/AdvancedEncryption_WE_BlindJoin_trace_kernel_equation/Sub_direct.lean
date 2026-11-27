import Mathlib
open Finset
theorem solution {K Z I : Type*} [CommRing K] [AddCommGroup Z] [Fintype I]
    (tr : K →+ Z) (L A : I → K → K)
    (hA : ∀ i b x, tr (b*L i x) = tr (A i b*x))
    (hnd : ∀ x, (∀ g, tr (g*x) = 0) → x = 0)
    (b t : K) (M : ℕ) (deg : I → ℕ) :
    (∀ g, tr (b*(g*t^M - ∑ i, L i (g*t^(deg i)))) = 0) ↔
      b*t^M - ∑ i, A i b*t^(deg i) = 0 := by
  have eqn (g : K) :
      tr (b*(g*t^M - ∑ i, L i (g*t^(deg i)))) =
      tr (g*(b*t^M - ∑ i, A i b*t^(deg i))) := by
    simp only [mul_sub, Finset.mul_sum, map_sub, map_sum, hA]
    congr 1
    · congr 1
      ring
    · apply Finset.sum_congr rfl
      intro i hi
      congr 1
      ring
  simp_rw [eqn]
  constructor
  · exact hnd _
  · intro h g
    simp [h]

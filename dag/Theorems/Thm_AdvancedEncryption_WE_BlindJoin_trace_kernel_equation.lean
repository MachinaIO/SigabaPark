import Mathlib
open Finset
theorem AdvancedEncryption.WE.BlindJoin.trace_kernel_equation {K Z I : Type*} [CommRing K] [AddCommGroup Z] [Fintype I]
    (tr : K →+ Z) (L A : I → K → K)
    (hA : ∀ i b x, tr (b*L i x) = tr (A i b*x))
    (hnd : ∀ x, (∀ g, tr (g*x) = 0) → x = 0)
    (b t : K) (M : ℕ) (deg : I → ℕ) :
    (∀ g, tr (b*(g*t^M - ∑ i, L i (g*t^(deg i)))) = 0) ↔
      b*t^M - ∑ i, A i b*t^(deg i) = 0 := by sorry

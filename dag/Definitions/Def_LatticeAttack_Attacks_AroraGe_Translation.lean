module

public import Mathlib.Algebra.Polynomial.Taylor

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.AroraGe

open Polynomial
variable {R ι : Type*} [CommRing R]

/-- Translation preserves every linear relation among rows modulo the constant term. -/
theorem translated_relation_iff (s : R) (I : Finset ι) (p : ι → R[X]) (w : ι → R)
    (c : R) :
    (∑ i ∈ I, w i • taylor s (p i)) = C c ↔ (∑ i ∈ I, w i • p i) = C c := by
  have h := (taylorEquiv s).injective.eq_iff
      (a := ∑ i ∈ I, w i • p i) (b := C c)
  change (taylor s (∑ i ∈ I, w i • p i) = taylor s (C c) ↔ _) at h
  simpa using h

/-- The positive coefficients vanish exactly when the polynomial is constant. -/
theorem positive_coeff_zero_iff (p : R[X]) :
    (∀ k : ℕ, p.coeff (k + 1) = 0) ↔ ∃ c : R, p = C c := by
  constructor
  · intro h
    refine ⟨p.coeff 0, ?_⟩
    ext n
    cases n with
    | zero => simp
    | succ n => simp [h n]
  · rintro ⟨c, rfl⟩ k
    simp

/-- Centered and translated positive-coefficient row arrays have identical row relations. -/
theorem translated_positive_relation_iff (s : R) (I : Finset ι) (p : ι → R[X]) (w : ι → R) :
    (∀ k : ℕ, (∑ i ∈ I, w i • taylor s (p i)).coeff (k + 1) = 0) ↔
      (∀ k : ℕ, (∑ i ∈ I, w i • p i).coeff (k + 1) = 0) := by
  rw [positive_coeff_zero_iff, positive_coeff_zero_iff]
  exact exists_congr (translated_relation_iff s I p w)

#print axioms translated_relation_iff
#print axioms positive_coeff_zero_iff
#print axioms translated_positive_relation_iff

end SigabaNeo.Lattices.AroraGe

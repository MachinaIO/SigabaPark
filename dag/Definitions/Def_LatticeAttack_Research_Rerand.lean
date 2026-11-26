import Mathlib

set_option autoImplicit true

/-! # Moments for a uniformly sampled nonzero linear form

Rows of the test matrix are the residues of lattice vectors in a chosen integral basis.
-/

namespace SigabaNeo.Rerand

open scoped NNReal

variable {p d t : ℕ} [Fact p.Prime]

/-- Remove the zero form from the annihilator of the tuple. -/
theorem nonzeroKernelCount (X : Matrix (Fin t) (Fin d) (ZMod p)) :
    ((Finset.univ.filter fun c ↦ X.mulVec c = 0).erase 0).card = p ^ (d - X.rank) - 1 := by
  classical
  rw [Finset.card_erase_of_mem (by simp), ← Fintype.card_subtype]
  let K := LinearMap.ker X.mulVecLin
  let e : {c // X.mulVec c = 0} ≃ K :=
    { toFun := fun c ↦ ⟨c.val, c.property⟩
      invFun := fun c ↦ ⟨c.val, c.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e]
  have h := X.mulVecLin.finrank_range_add_finrank_ker
  change X.rank + Module.finrank (ZMod p) K = _ at h
  simp at h
  have hk : Module.finrank (ZMod p) K = d - X.rank := by omega
  rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card, hk]

/-- Exact finite-support moment of any order, including dependent tuples.
For positive dimension the denominator counts all nonzero forms. -/
theorem meanValue {ι : Type*} (s : Finset ι)
    (X : ι → Matrix (Fin t) (Fin d) (ZMod p)) (F : ι → ℝ≥0) :
    (∑ c ∈ (Finset.univ.erase (0 : Fin d → ZMod p)), ∑ x ∈ s,
      if (X x).mulVec c = 0 then F x else 0) / ↑(p ^ d - 1 : ℕ) =
      ∑ x ∈ s, ↑(p ^ (d - (X x).rank) - 1 : ℕ) * F x / ↑(p ^ d - 1 : ℕ) := by
  classical
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have he : (Finset.univ.erase 0).filter (fun c ↦ (X x).mulVec c = 0) =
      (Finset.univ.filter fun c ↦ (X x).mulVec c = 0).erase 0 := by
    ext c
    simp [and_comm]
  rw [he, nonzeroKernelCount]

#print axioms nonzeroKernelCount
#print axioms meanValue

end SigabaNeo.Rerand

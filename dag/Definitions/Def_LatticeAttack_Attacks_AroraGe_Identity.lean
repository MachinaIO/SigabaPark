module

public import Definitions.Def_LatticeAttack_Attacks_AroraGe_Multi
import all Definitions.Def_LatticeAttack_Attacks_AroraGe_Multi

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.AroraGe.Multi

open MvPolynomial
open scoped BigOperators

variable {q n : ℕ} [Fact q.Prime]

private theorem sampleRow_prod (E : Finset (ZMod q)) (s a : Fin n → ZMod q) (e : ZMod q) :
    sampleRow E s a e = ∏ r ∈ E, (C (e + dotProduct a s) - ∑ i, a i • X i - C r) := by
  simp [sampleRow_eq, Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub]

theorem sampleRow_totalDegree_le (E : Finset (ZMod q)) (s a : Fin n → ZMod q) (e : ZMod q) :
    (sampleRow E s a e).totalDegree ≤ E.card := by
  rw [sampleRow_prod]
  apply (totalDegree_finsetProd ..).trans
  calc
    _ ≤ ∑ _r ∈ E, 1 := by
      apply Finset.sum_le_sum
      intro r _
      apply (totalDegree_sub_C_le ..).trans
      apply (totalDegree_sub ..).trans
      apply max_le (by rw [totalDegree_C]; decide)
      apply totalDegree_finsetSum_le
      intro i _
      exact (totalDegree_smul_le ..).trans (totalDegree_X i).le
    _ = _ := by simp

theorem eval_sampleRow (E : Finset (ZMod q)) (s a : Fin n → ZMod q) {e : ZMod q} (he : e ∈ E) :
    eval s (sampleRow E s a e) = 0 := by
  classical
  rw [sampleRow_prod, map_prod]
  apply Finset.prod_eq_zero he
  simp [dotProduct, smul_eq_C_mul]

noncomputable def monomialValues (s : Fin n → ZMod q) (D : ℕ) (d : indices n D) : ZMod q :=
  ∏ i, s i ^ d.val i

theorem mulVec_monomialValues (E : Finset (ZMod q)) (s : Fin n → ZMod q) {m : ℕ}
    (p : Fin m → ZMod q × (Fin n → ZMod q)) (hp : ∀ i, (p i).1 ∈ E) :
    (matrix E s p).mulVec (monomialValues s E.card) =
      -(fun i ↦ (sampleRow E s (p i).2 (p i).1).coeff 0) := by
  classical
  funext i
  let f := sampleRow E s (p i).2 (p i).1
  let I := indices n E.card
  let term := fun d : Fin n →₀ ℕ ↦ f.coeff d * ∏ j, s j ^ d j
  change (∑ d : I, term d.val) = -f.coeff 0
  rw [Finset.sum_coe_sort]
  have hz : (0 : Fin n →₀ ℕ) ∉ I := by
    intro h
    have := (Finset.mem_Icc.mp (bounds (⟨0, h⟩ : indices n E.card))).1
    simp [weight] at this
  have hs : f.support ⊆ insert 0 I := by
    intro d hd
    by_cases h : d = 0
    · simp [h]
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨weight d, Finset.mem_Icc.mpr ⟨?_, (le_totalDegree hd).trans
      (sampleRow_totalDegree_le ..)⟩, Finset.mem_finsuppAntidiag'.mpr ⟨rfl, by simp⟩⟩
    exact Nat.pos_of_ne_zero (fun hw ↦ h ((Finsupp.degree_eq_zero_iff d).mp hw))
  have hsum := Finset.sum_subset hs (f := term) (by
    intro d _ hd
    simp [term, notMem_support_iff.mp hd])
  have hev := eval_sampleRow E s (p i).2 (hp i)
  change eval s f = 0 at hev
  rw [eval_eq'] at hev
  change (∑ d ∈ f.support, term d) = 0 at hev
  rw [hsum, Finset.sum_insert hz] at hev
  exact eq_neg_of_add_eq_zero_left (by simpa [term, add_comm] using hev)

theorem single_mem_indices {D : ℕ} (hD : 1 ≤ D) (i : Fin n) :
    Finsupp.single i 1 ∈ indices n D := by
  apply Finset.mem_biUnion.mpr
  exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hD⟩, Finset.mem_finsuppAntidiag'.mpr
    ⟨by simp, by simp⟩⟩

theorem monomialValues_single (s : Fin n → ZMod q) {D : ℕ} (hD : 1 ≤ D) (i : Fin n) :
    monomialValues s D ⟨Finsupp.single i 1, single_mem_indices hD i⟩ = s i := by
  classical
  simp [monomialValues, Finsupp.single_apply]

#print axioms sampleRow_totalDegree_le
#print axioms eval_sampleRow
#print axioms mulVec_monomialValues
#print axioms monomialValues_single

end SigabaNeo.Lattices.AroraGe.Multi

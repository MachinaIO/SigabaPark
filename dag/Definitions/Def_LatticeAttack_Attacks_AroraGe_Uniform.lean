module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Prime.Factorial

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.AroraGe

open Polynomial

/-- With uniform translation in a set of D distinct roots, at most D-k translations
erase the coefficient of degree k, for every positive k ≤ D below the characteristic. -/
theorem uniformTranslation_zero_count {q : ℕ} [Fact q.Prime] (E : Finset (ZMod q))
    (hq : E.card < q) {k : ℕ} (hD : k ≤ E.card) :
    (E.filter fun e ↦ ((taylor e) (∏ r ∈ E, (X - C r))).coeff k = 0).card ≤ E.card - k := by
  classical
  let f := ∏ r ∈ E, (X - C r)
  have hd : f.natDegree = E.card := by
    simp [f, natDegree_prod_of_monic (f := fun r : ZMod q ↦ X - C r) (h := fun r _ ↦ monic_X_sub_C r)]
  have hm : f.Monic := monic_prod_X_sub_C id E
  have hc : (E.card.choose k : ZMod q) ≠ 0 := by
    intro hz
    have hv := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hf : q ∣ E.card.factorial := by
      rw [← Nat.choose_mul_factorial_mul_factorial hD]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hv _) _
    exact hq.not_ge ((Fact.out : q.Prime).dvd_factorial.mp hf)
  have hn : hasseDeriv k f ≠ 0 := by
    intro hz
    have h := congrArg (fun p : Polynomial (ZMod q) ↦ p.coeff (E.card - k)) hz
    simp only [hasseDeriv_coeff, Nat.sub_add_cancel hD, coeff_zero] at h
    rw [← hd, hm.coeff_natDegree, mul_one, hd] at h
    exact hc h
  change (E.filter fun e ↦ ((taylor e) f).coeff k = 0).card ≤ _
  apply le_trans (card_le_degree_of_subset_roots (p := hasseDeriv k f) ?_)
  · simpa [hd] using natDegree_hasseDeriv_le f k
  · intro e he
    apply (mem_roots hn).mpr
    simpa [taylor_coeff] using (Finset.mem_filter.mp he).2

#print axioms uniformTranslation_zero_count

end SigabaNeo.Lattices.AroraGe

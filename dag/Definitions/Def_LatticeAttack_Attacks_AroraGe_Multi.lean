module

public import Definitions.Def_LatticeAttack_Attacks_AroraGe_CenteredRank
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.FieldTheory.Finite.Polynomial

public import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.AroraGe.Multi

open MvPolynomial
open scoped BigOperators
variable {q n : ℕ} [Fact q.Prime]

noncomputable def indices (n D : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finset.Icc 1 D).biUnion (Finset.univ.finsuppAntidiag ·)

abbrev weight (d : Fin n →₀ ℕ) := d.sum (fun _ k ↦ k)

private theorem bounds {D : ℕ} (d : indices n D) : weight d.val ∈ Finset.Icc 1 D := by
  obtain ⟨k, hk, h⟩ := Finset.mem_biUnion.mp d.property
  rwa [weight, (Finset.mem_finsuppAntidiag'.mp h).1]

noncomputable def shifted (E : Finset (ZMod q)) (e : ZMod q) :=
  Polynomial.taylor e (∏ r ∈ E, (Polynomial.X - Polynomial.C r))

/-- The row in coordinates Y = secret - X. -/
noncomputable def row (E : Finset (ZMod q)) (e : ZMod q) (a : Fin n → ZMod q) :=
  (shifted E e).eval₂ MvPolynomial.C (∑ i, a i • MvPolynomial.X i)

private theorem row_coeff (E : Finset (ZMod q)) (e : ZMod q) (a : Fin n → ZMod q)
    (d : Fin n →₀ ℕ) :
    (row E e a).coeff d = (shifted E e).coeff (weight d) * d.multinomial *
      d.prod (fun i k ↦ a i ^ k) := by
  classical
  simp only [row, Polynomial.eval₂_eq_sum_range, coeff_sum, coeff_C_mul,
    coeff_linearCombination_X_pow_of_fintype, weight, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · ring
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

private noncomputable def pairing (E : Finset (ZMod q)) (e : ZMod q)
    (v : indices n E.card → ZMod q) : MvPolynomial (Fin n) (ZMod q) :=
  ∑ d, monomial d.val (v d * (shifted E e).coeff (weight d.val) * d.val.multinomial)

theorem exists_detecting_pair (E : Finset (ZMod q)) (hq : E.card < q)
    (v : indices n E.card → ZMod q) (hv : v ≠ 0) :
    ∃ e ∈ E, ∃ a, ∑ d, (row E e a).coeff d.val * v d ≠ 0 := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, v d ≠ 0 := by simpa [funext_iff] using hv
  obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp (bounds d)
  obtain ⟨e, he, hc⟩ : ∃ e ∈ E, (shifted E e).coeff (weight d.val) ≠ 0 := by
    by_contra! h
    have H := uniformTranslation_zero_count E hq hu
    change (E.filter fun e ↦ (shifted E e).coeff (weight d.val) = 0).card ≤ _ at H
    rw [Finset.filter_eq_self.mpr h] at H
    omega
  have hm : (d.val.multinomial : ZMod q) ≠ 0 := by
    intro h
    have dvd := (ZMod.natCast_eq_zero_iff ..).mp h
    have H := Nat.multinomial_spec d.val.support d.val
    have H' : q ∣ (weight d.val).factorial := H ▸ dvd_mul_of_dvd_right dvd _
    exact (hu.trans_lt hq).not_ge ((Fact.out : q.Prime).dvd_factorial.mp H')
  refine ⟨e, he, ?_⟩
  by_contra! h
  have hz : pairing E e v = 0 := by
    apply MvPolynomial.eq_zero_of_eval_eq_zero
    · intro a
      simpa [pairing, map_sum, eval_monomial, row_coeff, mul_comm, mul_left_comm,
        mul_assoc] using h a
    · apply restrictTotalDegree_le_restrictDegree
      rw [mem_restrictTotalDegree, ZMod.card]
      apply totalDegree_finsetSum_le
      intro j _
      exact (totalDegree_monomial_le ..).trans ((Finset.mem_Icc.mp (bounds j)).2.trans (by omega))
  have H := congrArg (fun p : MvPolynomial (Fin n) (ZMod q) ↦ p.coeff d.val) hz
  simp [pairing, coeff_monomial, hd, hc, hm] at H

/-- The substitution has intercept b = e + ⟨a,s⟩ and linear part -⟨a,X⟩. -/
noncomputable def sampleRow (E : Finset (ZMod q)) (s a : Fin n → ZMod q) (e : ZMod q) :=
  row E (e + dotProduct a s) (-a)

theorem sampleRow_eq (E : Finset (ZMod q)) (s a : Fin n → ZMod q) (e : ZMod q) :
    sampleRow E s a e = (∏ r ∈ E, (Polynomial.X - Polynomial.C r)).eval₂ MvPolynomial.C
      (MvPolynomial.C (e + dotProduct a s) - ∑ i, a i • MvPolynomial.X i) := by
  simp [sampleRow, row, shifted, Polynomial.taylor_apply, Polynomial.eval₂_comp,
    Polynomial.eval₂_add, sub_eq_add_neg, Finset.sum_neg_distrib, add_comm]

theorem sample_detects (E : Finset (ZMod q)) (hq : E.card < q) (s : Fin n → ZMod q)
    (v : indices n E.card → ZMod q) (hv : v ≠ 0) :
    ∃ e ∈ E, ∃ a, ∑ d, (sampleRow E s a e).coeff d.val * v d ≠ 0 := by
  classical
  obtain ⟨b, hb, a, ha⟩ := exists_detecting_pair E hq v hv
  let f := ∏ r ∈ E, (Polynomial.X - Polynomial.C r)
  let g : Polynomial (ZMod q) := ∑ d : indices n E.card,
    Polynomial.C ((d.val.multinomial : ZMod q) * d.val.prod (fun i k ↦ a i ^ k) * v d) *
      Polynomial.hasseDeriv (weight d.val) f
  have ev (x : ZMod q) : g.eval x = ∑ d, (row E x a).coeff d.val * v d := by
    simp [g, Polynomial.eval_prod, Polynomial.eval_finsetSum, row_coeff, shifted, Polynomial.taylor_coeff, f,
      mul_comm, mul_left_comm, mul_assoc]
  have gn : g ≠ 0 := by
    intro h
    exact ha (by rw [← ev, h, Polynomial.eval_zero])
  have pos := Finset.card_pos.mpr ⟨b, hb⟩
  have deg : g.natDegree ≤ E.card - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro d _
    apply (Polynomial.natDegree_C_mul_le ..).trans
    apply (Polynomial.natDegree_hasseDeriv_le ..).trans
    have hf : f.natDegree = E.card := by
      simp [f, Polynomial.natDegree_prod_of_monic
        (f := fun r : ZMod q ↦ Polynomial.X - Polynomial.C r) (h := fun r _ ↦ Polynomial.monic_X_sub_C r)]
    rw [hf]
    have := (Finset.mem_Icc.mp (bounds d)).1
    omega
  by_contra! h
  let t := dotProduct (-a) s
  have H := Polynomial.card_le_degree_of_subset_roots (p := g) (Z := E.image (· + t)) (by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    apply (Polynomial.mem_roots gn).mpr
    simpa [ev, sampleRow, t] using h e he (-a))
  rw [Finset.card_image_of_injective _ (add_left_injective t)] at H
  omega

noncomputable def failures (E : Finset (ZMod q)) (s : Fin n → ZMod q) (m : ℕ) :=
  (Finset.univ.erase (0 : indices n E.card → ZMod q)).biUnion fun v ↦
    Fintype.piFinset fun _ : Fin m ↦
      (E ×ˢ Finset.univ).filter fun p ↦ ∑ d, (sampleRow E s p.2 p.1).coeff d.val * v d = 0

theorem failures_card (E : Finset (ZMod q)) (hq : E.card < q) (s : Fin n → ZMod q) (m : ℕ) :
    (failures E s m).card ≤ (q ^ (indices n E.card).card - 1) * (E.card * q ^ n - 1) ^ m := by
  classical
  unfold failures
  have hc : (Finset.univ.erase (0 : indices n E.card → ZMod q)).card =
      q ^ (indices n E.card).card - 1 := by simp
  rw [← hc]
  apply Finset.card_biUnion_le_card_mul
  intro v hv
  rw [Fintype.card_piFinset_const]
  apply Nat.pow_le_pow_left
  obtain ⟨e, he, a, ha⟩ := sample_detects E hq s v (Finset.mem_erase.mp hv).1
  have hlt := Finset.card_lt_card ((Finset.filter_ssubset
    (p := fun p : ZMod q × (Fin n → ZMod q) ↦ ∑ d, (sampleRow E s p.2 p.1).coeff d.val * v d = 0)).mpr
      ⟨(e,a), Finset.mem_product.mpr ⟨he, Finset.mem_univ a⟩, ha⟩)
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card] at hlt
  omega

noncomputable def matrix (E : Finset (ZMod q)) (s : Fin n → ZMod q) {m : ℕ}
    (p : Fin m → ZMod q × (Fin n → ZMod q)) : Matrix (Fin m) (indices n E.card) (ZMod q) :=
  fun i d ↦ (sampleRow E s (p i).2 (p i).1).coeff d.val

theorem mem_failures_iff (E : Finset (ZMod q)) (s : Fin n → ZMod q) {m : ℕ}
    (p : Fin m → ZMod q × (Fin n → ZMod q)) (hp : ∀ i, (p i).1 ∈ E) :
    p ∈ failures E s m ↔ (matrix E s p).rank < (indices n E.card).card := by
  classical
  let A := matrix E s p
  have mem : p ∈ failures E s m ↔ ∃ v ≠ 0, A.mulVec v = 0 := by
    constructor
    · intro h
      obtain ⟨v, hv, hrows⟩ := Finset.mem_biUnion.mp h
      refine ⟨v, (Finset.mem_erase.mp hv).1, funext fun i ↦ ?_⟩
      exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hrows i)).2
    · rintro ⟨v, hv, hz⟩
      refine Finset.mem_biUnion.mpr ⟨v, Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩,
        Fintype.mem_piFinset.mpr fun i ↦ Finset.mem_filter.mpr ⟨?_, congrFun hz i⟩⟩
      exact Finset.mem_product.mpr ⟨hp i, Finset.mem_univ _⟩
  rw [mem]
  have h := A.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
  change (∃ v ≠ 0, A.mulVec v = 0) ↔ Module.finrank _ (LinearMap.range A.mulVecLin) < _
  rw [show Module.finrank (ZMod q) (LinearMap.range A.mulVecLin) < (indices n E.card).card ↔
      0 < Module.finrank (ZMod q) (LinearMap.ker A.mulVecLin) by omega,
      Nat.pos_iff_ne_zero, ne_eq, Submodule.finrank_eq_zero]
  exact ⟨fun ⟨v, hv, hz⟩ ↦ A.mulVecLin.ker.ne_bot_iff.mpr ⟨v, hz, hv⟩,
    fun h ↦ by obtain ⟨v, hz, hv⟩ := A.mulVecLin.ker.ne_bot_iff.mp h; exact ⟨v, hv, hz⟩⟩

theorem failure_probability (E : Finset (ZMod q)) (hne : E.Nonempty) (hq : E.card < q)
    (s : Fin n → ZMod q) (m : ℕ) :
    ((failures E s m).card : ℚ) / (E.card * (q : ℚ) ^ n) ^ m ≤
      (q ^ (indices n E.card).card - 1 : ℕ) *
        (1 - 1 / (E.card * (q : ℚ) ^ n)) ^ m := by
  let N := E.card * q ^ n
  have hE := Finset.card_pos.mpr hne
  have hq' := (Fact.out : q.Prime).pos
  have hn : 0 < N := Nat.mul_pos hE (pow_pos hq' _)
  have H := failures_card E hq s m
  change _ ≤ _ * (N - 1) ^ m at H
  have H' := (Nat.cast_le (α := ℚ)).mpr H
  push_cast [Nat.cast_sub hn] at H'
  have hN : (0 : ℚ) < N := by exact_mod_cast hn
  have heq : (N : ℚ) = E.card * (q : ℚ) ^ n := by simp [N]
  rw [← heq, div_le_iff₀ (pow_pos hN m), mul_assoc, ← mul_pow]
  convert H' using 1
  field_simp

#print axioms mem_failures_iff
#print axioms failure_probability
#print axioms exists_detecting_pair
#print axioms sampleRow_eq
#print axioms sample_detects
#print axioms failures_card

end SigabaNeo.Lattices.AroraGe.Multi

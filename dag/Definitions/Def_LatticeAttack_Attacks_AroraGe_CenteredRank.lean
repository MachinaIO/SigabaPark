module

public import Definitions.Def_LatticeAttack_Attacks_AroraGe_Uniform
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.AroraGe

open Polynomial
variable {q : ℕ} [Fact q.Prime]

/-- Pairing the nonconstant coefficients of f(e + aX) with a candidate kernel vector,
viewed as a polynomial in the row scalar a. -/
noncomputable def rowPairing (E : Finset (ZMod q)) (e : ZMod q)
    (v : Fin E.card → ZMod q) : Polynomial (ZMod q) :=
  ∑ i, monomial (i.val + 1) (v i * ((taylor e) (∏ r ∈ E, (X - C r))).coeff (i.val + 1))

theorem exists_detecting_pair (E : Finset (ZMod q)) (hq : E.card < q)
    (v : Fin E.card → ZMod q) (hv : v ≠ 0) :
    ∃ e ∈ E, ∃ a, (rowPairing E e v).eval a ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  let f := ∏ r ∈ E, (X - C r)
  obtain ⟨e, he, hc⟩ : ∃ e ∈ E, ((taylor e) f).coeff (i.val + 1) ≠ 0 := by
    by_contra! h
    have hh := uniformTranslation_zero_count E hq (k := i.val + 1) i.isLt
    change (E.filter fun e ↦ ((taylor e) f).coeff (i.val + 1) = 0).card ≤ _ at hh
    rw [Finset.filter_eq_self.mpr h] at hh
    have := i.isLt
    omega
  refine ⟨e, he, ?_⟩
  have hn : rowPairing E e v ≠ 0 := by
    intro hz
    have h := congrArg (fun p : Polynomial (ZMod q) ↦ p.coeff (i.val + 1)) hz
    simp [rowPairing, finsetSum_coeff, coeff_monomial, Fin.ext_iff.symm] at h
    exact hc (h.resolve_left hi)
  by_contra! h
  have hd : (rowPairing E e v).natDegree ≤ E.card := by
    apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_monomial_le _).trans j.isLt
  have hh := card_le_degree_of_subset_roots (p := rowPairing E e v)
    (Z := Finset.univ) (fun a _ ↦ (mem_roots hn).mpr (h a))
  simp at hh
  omega

/-- Sample sequences whose centered nonconstant coefficient rows have a nontrivial kernel. -/
noncomputable def centeredRankFailures (E : Finset (ZMod q)) (m : ℕ) :=
  (Finset.univ.erase (0 : Fin E.card → ZMod q)).biUnion fun v ↦
    Fintype.piFinset fun _ : Fin m ↦
      (E ×ˢ Finset.univ).filter fun p ↦ (rowPairing E p.1 v).eval p.2 = 0

theorem centeredRankFailures_card (E : Finset (ZMod q)) (hq : E.card < q) (m : ℕ) :
    (centeredRankFailures E m).card ≤ (q ^ E.card - 1) * (E.card * q - 1) ^ m := by
  classical
  unfold centeredRankFailures
  have hc : (Finset.univ.erase (0 : Fin E.card → ZMod q)).card = q ^ E.card - 1 := by simp
  rw [← hc]
  apply Finset.card_biUnion_le_card_mul
  intro v hv
  rw [Fintype.card_piFinset_const]
  apply Nat.pow_le_pow_left
  obtain ⟨e, he, a, ha⟩ := exists_detecting_pair E hq v (Finset.mem_erase.mp hv).1
  have hlt := Finset.card_lt_card ((Finset.filter_ssubset (p := fun p : ZMod q × ZMod q ↦ (rowPairing E p.1 v).eval p.2 = 0)).mpr
    ⟨(e,a), Finset.mem_product.mpr ⟨he, Finset.mem_univ a⟩, ha⟩)
  simp at hlt
  omega

/-- Matrix of the positive-degree coefficients in the centered coordinate. -/
noncomputable def centeredMatrix (E : Finset (ZMod q)) {m : ℕ}
    (p : Fin m → ZMod q × ZMod q) : Matrix (Fin m) (Fin E.card) (ZMod q) :=
  fun j i ↦ ((taylor (p j).1) (∏ r ∈ E, (X - C r))).coeff (i.val + 1) * (p j).2 ^ (i.val + 1)

theorem mem_centeredRankFailures_iff (E : Finset (ZMod q)) {m : ℕ}
    (p : Fin m → ZMod q × ZMod q) (hp : ∀ j, (p j).1 ∈ E) :
    p ∈ centeredRankFailures E m ↔ ∃ v ≠ 0, (centeredMatrix E p).mulVec v = 0 := by
  classical
  simp [centeredRankFailures, Fintype.mem_piFinset, hp, funext_iff (f := Matrix.mulVec _ _),
    Matrix.mulVec, dotProduct, centeredMatrix, rowPairing, eval_finsetSum, mul_comm,
    mul_left_comm]

#print axioms mem_centeredRankFailures_iff
#print axioms exists_detecting_pair
#print axioms centeredRankFailures_card

end SigabaNeo.Lattices.AroraGe

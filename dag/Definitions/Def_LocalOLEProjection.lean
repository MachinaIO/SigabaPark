import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.FieldDivision

namespace LocalOLEProjection

/-- All of the first table, with the second table restricted by its public domain. -/
def idealView {X F : Type*} [AddMonoid F] (A B : X → Bool)
    (b : F) (c : X → F) : (X → F) × ({i : X // B i = true} → F) :=
  (c, fun i => c i + if A i then b else 0)

theorem disjointView {X F : Type*} [AddMonoid F] (A B : X → Bool)
    (disj : ∀ i, B i = true → A i = false) (b : F) (c : X → F) :
    idealView A B b c = idealView A B 0 c := by
  unfold idealView
  congr 1
  funext i
  simp [disj i i.property]

theorem witnessView {X F : Type*} [AddCommGroup F] (A B : X → Bool)
    (b : F) (c : X → F) (i : X) (ha : A i = true) (hb : B i = true) :
    (idealView A B b c).2 ⟨i,hb⟩ - (idealView A B b c).1 i = b := by
  simp [idealView, ha]

/-- The real issuer uses only the two canonical quotient maps and a constant. -/
def issue {R : Type*} [CommRing R] (I J : Ideal R) (b : R)
    (r : R ⧸ (I * J)) : (R ⧸ I) × (R ⧸ J) :=
  (Ideal.Quotient.factor Ideal.mul_le_left r,
    Ideal.Quotient.factor Ideal.mul_le_right r + Ideal.Quotient.mk J b)

/-- Only the proof uses comaximality. Every possible complete pair of keys has
exactly one nonce in the product quotient, for every payload. -/
theorem uniqueNonce {R : Type*} [CommRing R] (I J : Ideal R) (h : IsCoprime I J)
    (b : R) (v : (R ⧸ I) × (R ⧸ J)) : ∃! r, issue I J b r = v := by
  let e := Ideal.quotientMulEquivQuotientProd I J h
  let w : (R ⧸ I) × (R ⧸ J) := (v.1, v.2 - Ideal.Quotient.mk J b)
  have char : ∀ r, issue I J b r = v ↔ e r = w := by
    intro r
    constructor
    · intro hv
      apply Prod.ext
      · simpa [e, issue, w] using congrArg Prod.fst hv
      · have eq2 := congrArg Prod.snd hv
        simpa [e, w] using (eq_sub_iff_add_eq.mpr (show
          Ideal.Quotient.factor Ideal.mul_le_right r + Ideal.Quotient.mk J b = v.2 from eq2))
    · intro hv
      apply Prod.ext
      · simpa [e, issue, w] using congrArg Prod.fst hv
      · have eq2 := congrArg Prod.snd hv
        simpa [issue] using (eq_sub_iff_add_eq.mp (show
          Ideal.Quotient.factor Ideal.mul_le_right r = v.2 - Ideal.Quotient.mk J b by
          simpa [e,w] using eq2))
  refine ⟨e.symm w, (char _).2 (e.apply_symm_apply w), ?_⟩
  intro r hr
  exact e.injective (((char r).1 hr).trans (e.apply_symm_apply w).symm)

open Polynomial

/-- Concrete remainder keys and field recovery for each rational common root. -/
noncomputable def polyKeys {F : Type*} [Field F] (f g p : F[X]) (b : F) : F[X] × F[X] :=
  (p % f, (p + C b) % g)

theorem rootRecovers {F : Type*} [Field F] (f g p : F[X]) (b z : F)
    (hf : f.eval z = 0) (hg : g.eval z = 0) :
    (polyKeys f g p b).2.eval z - (polyKeys f g p b).1.eval z = b := by
  simp [polyKeys, eval_mod_eq_self_of_root hf, eval_mod_eq_self_of_root hg]

/-- Surjectivity transfers a common label to a single address. -/
theorem commonLabel {X Z : Type*} (t : X → Z) (ht : Function.Surjective t)
    (a b : Z → Prop) : (∃ x, a (t x) ∧ b (t x)) ↔ ∃ z, a z ∧ b z := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨t x, hx⟩
  · rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := ht z
    exact ⟨x, hz⟩

/-- Several local failure tests can generate a common additive mask. -/
def idealHeader {R : Type*} [CommRing R] {n : ℕ} (f u : Fin n → R) (b : R) : R :=
  b + ∑ j, f j * u j

/-- A proof-only unit-ideal certificate translates all coins simultaneously. -/
theorem coinShift {R : Type*} [CommRing R] {n : ℕ} (f u t : Fin n → R) (b : R)
    (ht : ∑ j, f j * t j = 1) :
    idealHeader f (fun j => u j + b * t j) 0 = idealHeader f u b := by
  simp only [idealHeader, zero_add, mul_add, Finset.sum_add_distrib]
  have split : ∀ j, f j * (b * t j) = b * (f j * t j) := by
    intro j
    ac_rfl
  simp only [split, ← Finset.mul_sum, ht, mul_one, add_comm]

theorem headerWitness {R F : Type*} [CommRing R] [CommRing F] {n : ℕ}
    (ev : R →+* F) (f u : Fin n → R) (b : R) (h : ∀ j, ev (f j) = 0) :
    ev (idealHeader f u b) = ev b := by
  simp [idealHeader, map_sum, h]

/-- In characteristic two a Boolean-valued circuit identically zero on a
candidate domain only needs a random bit, once its canonical residue is known. -/
def bitMasked {R : Type*} [CommRing R] (c : R) (coin b : Bool) : R :=
  (if Bool.xor coin b then 1 else 0) + (if coin then c else 0)

theorem bitMaskedNo {R : Type*} [CommRing R] (coin : Bool) :
    bitMasked (0 : R) (!coin) true = bitMasked 0 coin false := by
  cases coin <;> simp [bitMasked]

theorem bitMaskedYes {R F : Type*} [CommRing R] [CommRing F] (ev : R →+* F)
    (two : (1 : F) + 1 = 0) (c : R) (hc : ev c = 1) (coin b : Bool) :
    ev (bitMasked c coin b) = if b then 1 else 0 := by
  cases coin <;> cases b <;> simp [bitMasked, hc, two]

end LocalOLEProjection

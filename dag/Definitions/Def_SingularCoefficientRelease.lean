import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace SingularCoefficientRelease

open Polynomial

/-- A separator for a privately unknown set of reachable nonzero determinants.
    The proof uses the set, but the actual mask sampler need only know its size bound. -/
noncomputable def separator {K : Type*} [Field K] (E : Finset K) : K[X] :=
  1 - ∏ a ∈ E, (1 - C a⁻¹ * X)

theorem separator_zero {K : Type*} [Field K] (E : Finset K) :
    (separator E).eval 0=0 := by simp [separator, Polynomial.eval_prod]

theorem separator_one {K : Type*} [Field K] (E : Finset K) (a : K)
    (ha : a ∈ E) (hn : a ≠ 0) : (separator E).eval a=1 := by
  classical
  simp only [separator, eval_sub, eval_one, Polynomial.eval_prod, eval_mul, eval_C, eval_X]
  have hz : (∏ i ∈ E, (1-i⁻¹*a))=0 := Finset.prod_eq_zero ha (by simp [hn])
  rw [hz, sub_zero]

theorem separator_degree {K : Type*} [Field K] (E : Finset K) :
    (separator E).natDegree ≤ E.card := by
  unfold separator
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · apply (Polynomial.natDegree_prod_le E (fun a => 1-C a⁻¹*X)).trans
    calc
      _ ≤ ∑ _i ∈ E, 1 := Finset.sum_le_sum (fun i _ => by
        apply (Polynomial.natDegree_sub_le _ _).trans
        apply max_le
        · simp
        · simpa using Polynomial.natDegree_C_mul_le (i : K)⁻¹ X)
      _ = E.card := by simp

/-- Once the whole vector of point values agrees, any deterministic canonical encoder
    acting on those values (including a Boolean coefficient serializer) agrees bit for bit. -/
theorem canonical_translate {K G X D : Type*} [Field K] [AddCommGroup G]
    (e : Finset K) (z : X → K) (mem : ∀ x, z x ∈ e) (nz : ∀ x, z x ≠ 0)
    (tr : K →+ G) (r : K[X]) (b g : K) (serialize : (X → G) → D) :
    serialize (fun x => tr ((r + C g * separator e).eval (z x) + b)) =
      serialize (fun x => tr (r.eval (z x) + (b+g))) := by
  congr 1
  funext x
  simp [separator_one e (z x) (mem x) (nz x), add_assoc, add_comm]

theorem pole_decode {K G : Type*} [Field K] [AddCommGroup G]
    (tr : K →+ G) (r : K[X]) (b : K) (zero : r.eval 0=0) :
    tr (r.eval 0+b)=tr b := by rw [zero,zero_add]

/-- The exact full-matrix translation over any commutative coefficient ring on the
    determinant-one locus. Over the binary field this is the entire regular locus. -/
theorem translate_matrix {K I : Type*} [CommRing K] [Fintype I] [DecidableEq I]
    (M R : Matrix I I K) (b : Matrix I I K) (h : M.det=1) :
    M * (R + M.adjugate) + b = M*R + (b + 1) := by
  rw [mul_add,Matrix.mul_adjugate,h,one_smul]
  abel

/-- A singular witness uses a nonzero left kernel vector; any nonzero output coordinate
    of that vector decodes the scalar bit. -/
theorem kernel_decode {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (M R : Matrix I I K) (u : I → K) (b : K) (h : Matrix.vecMul u M=0) :
    Matrix.vecMul u (M*R+b • (1 : Matrix I I K))=b • u := by
  rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, h, Matrix.zero_vecMul,
      Matrix.vecMul_smul, Matrix.vecMul_one, zero_add]

def maskGroup (K : Type*) [Field K] (m : Nat) : AddSubgroup K[X] where
  carrier := {p | p.eval 0=0 ∧ p.natDegree ≤ m}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact ⟨by simp [ha.1,hb.1], (Polynomial.natDegree_add_le _ _).trans (max_le ha.2 hb.2)⟩
  neg_mem' := by
    intro a ha
    exact ⟨by simp [ha.1], by simpa using ha.2⟩

instance finiteMask {K : Type*} [Field K] [Finite K] (m : Nat) : Finite (maskGroup K m) := by
  apply Finite.of_injective (fun p : maskGroup K m => fun i : Fin (m+1) => p.val.coeff i)
  intro p q h
  apply Subtype.ext
  ext i
  by_cases hi : i≤m
  · exact congrFun h ⟨i, by omega⟩
  · have hp := p.property.2
    have hq := q.property.2
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show p.val.natDegree < i by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (show q.val.natDegree < i by omega)]

noncomputable def delta {K : Type*} [Field K] {m : Nat} (E : Finset K)
    (size : E.card ≤ m) (g : K) : maskGroup K m :=
  ⟨C g * separator E, by
    exact ⟨by simp [separator_zero],
      (Polynomial.natDegree_C_mul_le _ _).trans ((separator_degree E).trans size)⟩⟩

noncomputable def shiftCoins {K : Type*} [Field K] {m : Nat} (E : Finset K)
    (size : E.card ≤ m) (g : K) : maskGroup K m ≃ maskGroup K m where
  toFun p := p + delta E size g
  invFun p := p - delta E size g
  left_inv := by intro p; simp
  right_inv := by intro p; simp

def view {K G W O : Type*} [Field K] [AddCommGroup G] {m : Nat}
    (tr : K →+ G) (z : W → K) (encode : (W → G) → O) (b : K) (p : maskGroup K m) :=
  encode (fun w => tr (p.val.eval (z w)+b))

theorem viewCoupling {K G W O : Type*} [Field K] [AddCommGroup G] {m : Nat}
    (E : Finset K) (size : E.card ≤ m) (z : W → K)
    (mem : ∀ w, z w ∈ E) (nz : ∀ w, z w ≠ 0) (tr : K →+ G)
    (encode : (W → G) → O) (b₀ b₁ : K) (p : maskGroup K m) :
    view tr z encode b₁ (shiftCoins E size (b₀-b₁) p) = view tr z encode b₀ p := by
  change encode (fun w => tr ((p.val+C (b₀-b₁)*separator E).eval (z w)+b₁)) = _
  rw [canonical_translate E z mem nz tr p.val b₁ (b₀-b₁) encode]
  simp [view]

/-- Any predicate of the whole canonical description can be used here. -/
noncomputable def eventEquiv {K G W O : Type*} [Field K] [AddCommGroup G] {m : Nat}
    (E : Finset K) (size : E.card ≤ m) (z : W → K)
    (mem : ∀ w, z w ∈ E) (nz : ∀ w, z w ≠ 0) (tr : K →+ G)
    (encode : (W → G) → O) (b₀ b₁ : K) (event : O → Prop) :
    {p : maskGroup K m // event (view tr z encode b₀ p)} ≃
      {p : maskGroup K m // event (view tr z encode b₁ p)} := by
  let e := shiftCoins E size (b₀-b₁)
  have eq : ∀ p, view tr z encode b₁ (e p) = view tr z encode b₀ p :=
    viewCoupling E size z mem nz tr encode b₀ b₁
  refine ⟨fun p => ⟨e p.val, (eq p.val).symm ▸ p.property⟩, fun p =>
    ⟨e.symm p.val, by simpa only [← eq, Equiv.apply_symm_apply] using p.property⟩, ?_, ?_⟩
  · intro p; apply Subtype.ext; simp
  · intro p; apply Subtype.ext; simp

end SingularCoefficientRelease

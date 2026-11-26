module

public import Definitions.Def_LatticeAttack_Reduction_Slide_Loop
public import Definitions.Def_LatticeAttack_Reduction_LLL_Termination
public import Mathlib.LinearAlgebra.FreeModule.PID
import all Definitions.Def_LatticeAttack_Reduction_Slide_SVP

set_option autoImplicit true

public section
namespace SigabaNeo.Slide
open Matrix LLL.Algorithm
variable {n d : ℕ}

/-- Every common integer factor of the exact solver's coefficients is a unit. -/
theorem dualSolveAt_primitive (B : Matrix (Fin n) (Fin d) ℤ) (p k : ℕ) (fit : p + k ≤ n) (pos : 0 < k)
    (hr : ((blockAt B p k fit) * (blockAt B p k fit).transpose).det ≠ 0)
    (t : ℤ) (z : Fin k → ℤ) (factor : dualSolveAt B p k fit pos = fun i ↦ t * z i) :
    t = 1 ∨ t = -1 := by
  let A := dualRows (blockAt B p k fit)
  obtain ⟨nz, best⟩ := dualSolveAt_spec B p k fit pos hr
  have scale : vector A (dualSolveAt B p k fit pos) = (t : ℚ) • vector A z := by
    rw [factor]
    unfold vector
    rw [← Matrix.smul_vecMul]
    congr 1
    ext i
    simp
  change vector A _ ≠ 0 at nz
  rw [scale] at nz
  have nt : t ≠ 0 := by rintro rfl; simp at nz
  have nv : vector A z ≠ 0 := by intro h; simp [h] at nz
  have h := best z (by rintro rfl; apply nv; exact Matrix.zero_vecMul A)
  change weight A _ ≤ weight A z at h
  unfold weight at h
  simp only [scale, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum] at h
  obtain ⟨j, hj⟩ : ∃ j, vector A z j ≠ 0 := by
    by_contra! all
    exact nv (funext all)
  have hp : 0 < ∑ i, vector A z i ^ 2 :=
    Finset.sum_pos' (fun i _ ↦ sq_nonneg _) ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero hj⟩
  have small : (t : ℚ)^2 ≤ 1 := by
    by_contra! big
    nlinarith [mul_pos (sub_pos.mpr big) hp]
  have small' : t^2 ≤ 1 := by exact_mod_cast small
  have lo : -1 ≤ t := by nlinarith [sq_nonneg (t+2)]
  have hi : t ≤ 1 := by nlinarith [sq_nonneg (t-2)]
  omega

/-- Integral change of coordinates carrying a primitive column to a chosen unit column. -/
theorem primitive_completion {k : ℕ} (s : Fin k → ℤ) (last : Fin k) (hs : s ≠ 0)
    (prim : ∀ t (z : Fin k → ℤ), s = t • z → t = 1 ∨ t = -1) :
    ∃ U V : Matrix (Fin k) (Fin k) ℤ, V * U = 1 ∧ U *ᵥ s = Pi.single last 1 := by
  classical
  let N := Submodule.span ℤ {s}
  let sn := N.smithNormalForm (Pi.basisFun ℤ (Fin k))
  let S := sn.2
  have mem : s ∈ N := Submodule.subset_span (by simp)
  have ne : Nonempty (Fin sn.1) := by
    by_contra! h
    let := h
    have e := S.bN.sum_repr (⟨s,mem⟩ : N)
    simp at e
    exact hs (congrArg Subtype.val e.symm)
  let i := ne.some
  let b := S.bM.reindex (Equiv.swap (S.f i) last)
  have eb : b last = S.bM (S.f i) := by simp [b]
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (S.bN i).property
  have rel : c • s = S.a i • b last := hc.trans ((S.snf i).trans (by rw [eb]))
  have cn : c ≠ 0 := by
    rintro rfl
    exact S.bN.ne_zero i (Subtype.ext (by simpa using hc.symm))
  let t := b.equivFun s last
  have coords : s = t • b last := by
    apply b.equivFun.injective
    rw [map_smul]
    ext j
    by_cases h : last = j
    · subst j; simp only [Pi.smul_apply, Module.Basis.equivFun_self, ite_true, smul_eq_mul, mul_one, t]
    · have e := congrFun (congrArg b.equivFun rel) j
      simp only [map_smul, Pi.smul_apply, Module.Basis.equivFun_self, ite_eq_right h, smul_eq_mul, mul_zero, mul_eq_zero, cn, false_or] at e ⊢
      exact e
  let U := LinearMap.toMatrix' b.equivFun.toLinearMap
  let V := LinearMap.toMatrix' b.equivFun.symm.toLinearMap
  have inv : V * U = 1 := by
    dsimp only [V,U]
    rw [← LinearMap.toMatrix'_comp]
    simp
  have image : U *ᵥ s = t • Pi.single last 1 := by
    dsimp only [U]
    rw [LinearMap.toMatrix'_mulVec, coords, map_smul]
    congr 1
    ext j
    simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
  rcases prim t _ coords with h | h
  · exact ⟨U,V,inv,by simpa [h] using image⟩
  · exact ⟨-U,-V,by simpa using inv,by simp [neg_mulVec, image, h]⟩

#print axioms primitive_completion

/-- The exact reciprocal SVP solution pairs to one with the new last projected row
and to zero with all preceding projected rows of the block. -/
theorem dual_completion (B : Rows n d) (p k : ℕ) (fit : p + k ≤ n) (pos : 0 < k)
    (hr : ((blockAt B p k fit) * (blockAt B p k fit).transpose).det ≠ 0) :
    let A := blockAt B p k fit
    let w := vector (dualRows A) (dualSolveAt B p k fit pos)
    ∃ U V : Matrix (Fin k) (Fin k) ℤ, V * U = 1 ∧
      (U.map (Int.castRingHom ℚ) * A) *ᵥ w = Pi.single ⟨k-1, by omega⟩ 1 ∧
      ∀ X : Matrix (Fin k) (Fin d) ℤ, lattice (U * X) = lattice X := by
  dsimp only
  let A := blockAt B p k fit
  let s := dualSolveAt B p k fit pos
  let l : Fin k := ⟨k-1, by omega⟩
  have ns : s ≠ 0 := by
    intro h
    have ne := (dualSolveAt_spec B p k fit pos hr).1
    change vector (dualRows A) s ≠ 0 at ne
    rw [h] at ne
    exact ne (Matrix.zero_vecMul _)
  obtain ⟨U,V,inv,eq⟩ := primitive_completion s l ns
    (fun t z h ↦ dualSolveAt_primitive B p k fit pos hr t z h)
  refine ⟨U,V,inv,?_,fun X ↦ lattice_completion X U V inv⟩
  change (U.map (Int.castRingHom ℚ) * A) *ᵥ vector (dualRows A) s = _
  rw [← mulVec_mulVec, vector, ← mulVec_transpose, mulVec_mulVec (M := A), reciprocal_pairing A hr,
    one_mulVec]
  ext j
  have hj := congrArg (Int.castRingHom ℚ) (congrFun eq j)
  simpa [mulVec, dotProduct, Pi.single_apply, l, apply_ite] using hj

#print axioms dual_completion
/-- Apply an integer row operation inside the flat interval [p,p+k). -/
def changeAt {k : ℕ} (p : ℕ) (fit : p + k ≤ n) (U : Matrix (Fin k) (Fin k) ℤ)
    (B : Matrix (Fin n) (Fin d) ℤ) : Matrix (Fin n) (Fin d) ℤ := fun i ↦
  if h : p ≤ i.val ∧ i.val < p + k then
    (U * (show Matrix (Fin k) (Fin d) ℤ from fun a ↦ B ⟨p+a.val, by omega⟩)) ⟨i.val-p, by omega⟩
  else B i

private theorem inside {k : ℕ} (p : ℕ) (fit : p+k ≤ n) (U : Matrix (Fin k) (Fin k) ℤ)
    (B : Matrix (Fin n) (Fin d) ℤ) :
    (show Matrix (Fin k) (Fin d) ℤ from fun a ↦ changeAt p fit U B ⟨p+a.val, by omega⟩) =
      U * (show Matrix (Fin k) (Fin d) ℤ from fun a ↦ B ⟨p+a.val, by omega⟩) := by
  ext a j
  simp [changeAt, a.isLt]

private theorem changeAt_mul {k m : ℕ} (p : ℕ) (fit : p+k ≤ n)
    (U : Matrix (Fin k) (Fin k) ℤ) (A : Matrix (Fin n) (Fin m) ℤ)
    (B : Matrix (Fin m) (Fin d) ℤ) :
    changeAt p fit U (A * B) = changeAt p fit U A * B := by
  ext i j
  by_cases h : p ≤ i.val ∧ i.val < p+k
  · let S : Matrix (Fin k) (Fin m) ℤ := fun a ↦ A ⟨p+a.val, by omega⟩
    have sel : (show Matrix (Fin k) (Fin d) ℤ from fun a ↦ (A * B) ⟨p+a.val, by omega⟩) = S * B := by
      ext a u; rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [changeAt, dite_eq_left h, sel]
    rw [← Matrix.mul_assoc, Matrix.mul_apply]
    simp [Matrix.mul_apply, changeAt, h, S]
  · simp [Matrix.mul_apply, changeAt, h]

private theorem changeAt_undo {k : ℕ} (p : ℕ) (fit : p+k ≤ n)
    (U V : Matrix (Fin k) (Fin k) ℤ) (inv : V * U = 1)
    (B : Matrix (Fin n) (Fin d) ℤ) : changeAt p fit V (changeAt p fit U B) = B := by
  ext i j
  by_cases h : p ≤ i.val ∧ i.val < p+k
  · simp only [changeAt, dite_eq_left h] at *
    change (V * (show Matrix (Fin k) (Fin d) ℤ from fun a ↦ changeAt p fit U B ⟨p+a.val, by omega⟩)) _ j = _
    rw [inside, ← Matrix.mul_assoc, inv, Matrix.one_mul]
    congr 2
    dsimp
    omega
  · simp [changeAt, h]

private theorem flat_matrix {k : ℕ} (p : ℕ) (fit : p+k ≤ n)
    (U : Matrix (Fin k) (Fin k) ℤ) (B : Matrix (Fin n) (Fin d) ℤ) :
    changeAt p fit U B = changeAt p fit U (1 : Matrix (Fin n) (Fin n) ℤ) * B := by
  simpa using changeAt_mul p fit U (1 : Matrix (Fin n) (Fin n) ℤ) B

theorem changeAt_preserves {k : ℕ} (p : ℕ) (fit : p+k ≤ n)
    (U V : Matrix (Fin k) (Fin k) ℤ) (inv : V * U = 1) (B : Matrix (Fin n) (Fin d) ℤ) :
    lattice (changeAt p fit U B) = lattice B := by
  rw [flat_matrix]
  apply lattice_completion B _ (changeAt p fit V 1)
  rw [← flat_matrix, changeAt_undo p fit U V inv]

#print axioms changeAt_preserves
/-- Prefixes disjoint from or containing the updated interval retain their determinant. -/
theorem changeAt_prefix {k : ℕ} (p : ℕ) (fit : p+k ≤ n)
    (U V : Matrix (Fin k) (Fin k) ℤ) (inv : V * U = 1) (B : Matrix (Fin n) (Fin d) ℤ)
    (j : Fin n) (outside : j.val < p ∨ p+k ≤ j.val+1) :
    gramDet (prefixRows (changeAt p fit U B) j) = gramDet (prefixRows B j) := by
  rcases outside with hj | hj
  · congr 1
    ext a u
    have h : ¬p ≤ a.val := by omega
    simp [prefixRows, changeAt, h]
  · let A := prefixRows B j
    have restrict : prefixRows (changeAt p fit U B) j = changeAt p hj U A := by
      ext a u
      by_cases h : p ≤ a.val ∧ a.val < p+k <;> simp [prefixRows,changeAt,A,h]
    let T := changeAt p hj U (1 : Matrix (Fin (j.val+1)) (Fin (j.val+1)) ℤ)
    let S := changeAt p hj V (1 : Matrix (Fin (j.val+1)) (Fin (j.val+1)) ℤ)
    have hi : S * T = 1 := by
      dsimp only [S,T]
      rw [← flat_matrix, changeAt_undo p hj U V inv]
    have hu : IsUnit T.det := isUnit_iff_dvd_one.mpr ⟨S.det, by
      simpa [det_mul, mul_comm] using (congrArg Matrix.det hi).symm⟩
    rw [restrict, flat_matrix]
    change ((T * A) * (T * A).transpose).det = (A * A.transpose).det
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc A, det_mul, det_mul, det_transpose]
    rcases Int.isUnit_iff.mp hu with h | h <;> simp [h]

theorem blockAt_changeAt {k : ℕ} (p : ℕ) (fit : p+k ≤ n)
    (U : Matrix (Fin k) (Fin k) ℤ) (B : Matrix (Fin n) (Fin d) ℤ) :
    blockAt (changeAt p fit U B) p k fit = U.map (Int.castRingHom ℚ) * blockAt B p k fit := by
  let P : Block p d := fun i j ↦ (B ⟨i.val, by omega⟩ j : ℚ)
  let X : Matrix (Fin k) (Fin d) ℤ := fun a ↦ B ⟨p+a.val, by omega⟩
  have pre : (fun (i : Fin p) (j : Fin d) ↦
      (changeAt p fit U B ⟨i.val, by omega⟩ j : ℚ)) = P := by
    ext i u
    simp [changeAt, P, i.isLt.not_ge]
  unfold blockAt
  rw [pre]
  have sub : (fun (i : Fin k) (j : Fin d) ↦
      (changeAt p fit U B ⟨p+i.val, by omega⟩ j : ℚ)) =
      (U * X).map (Int.castRingHom ℚ) := by
    ext i j
    exact congrArg (Int.castRingHom ℚ) (congrFun (congrFun (inside p fit U B) i) j)
  rw [sub, Matrix.map_mul]
  change projected P _ = _ * projected P (X.map (Int.castRingHom ℚ))
  unfold projected
  rw [Matrix.mul_sub]
  simp only [Matrix.mul_assoc]

#print axioms changeAt_prefix
#print axioms blockAt_changeAt
/-- Place the exact primal solution in the first projected row. -/
theorem primal_update (B : Matrix (Fin n) (Fin d) ℤ) (p k : ℕ)
    (fit : p+k ≤ n) (pos : 0 < k)
    (hr : ((blockAt B p k fit) * (blockAt B p k fit).transpose).det ≠ 0) :
    ∃ U V : Matrix (Fin k) (Fin k) ℤ, V * U = 1 ∧
      blockAt (changeAt p fit U B) p k fit ⟨0,pos⟩ =
        vector (blockAt B p k fit) (solveAt B p k fit pos) := by
  let s := solveAt B p k fit pos
  let o : Fin k := ⟨0,pos⟩
  have ns : s ≠ 0 := by
    intro h
    have ne := (solveAt_spec B p k fit pos hr).1
    change vector _ s ≠ 0 at ne
    rw [h] at ne
    exact ne (Matrix.zero_vecMul _)
  obtain ⟨T,S,inv,eq⟩ := primitive_completion s o ns
    (fun t z h ↦ solveAt_primitive B p k fit pos hr t z h)
  have col := congrArg (fun x ↦ S *ᵥ x) eq
  simp only [mulVec_mulVec, inv, one_mulVec, mulVec_single_one] at col
  refine ⟨S.transpose,T.transpose,?_,?_⟩
  · simpa using congrArg Matrix.transpose inv
  · rw [blockAt_changeAt]
    ext j
    simp only [vector, vecMul, dotProduct, Matrix.mul_apply, map_apply, transpose_apply]
    apply Finset.sum_congr rfl
    intro a _
    change (S a o : ℚ) * _ = (s a : ℚ) * _
    rw [congrFun col a]
    rfl

/-- The selected reciprocal vector on the actual updated rows. -/
theorem shifted_update (B : Matrix (Fin n) (Fin d) ℤ) (p k : ℕ)
    (fit : p+k ≤ n) (pos : 0 < k)
    (hr : ((blockAt B p k fit) * (blockAt B p k fit).transpose).det ≠ 0) :
    let w := vector (dualRows (blockAt B p k fit)) (dualSolveAt B p k fit pos)
    ∃ U V : Matrix (Fin k) (Fin k) ℤ, V * U = 1 ∧
      blockAt (changeAt p fit U B) p k fit *ᵥ w = Pi.single ⟨k-1, by omega⟩ 1 ∧
      lattice (changeAt p fit U B) = lattice B := by
  obtain ⟨U,V,inv,pair,_⟩ := dual_completion B p k fit pos hr
  exact ⟨U,V,inv,by rwa [blockAt_changeAt],changeAt_preserves p fit U V inv B⟩

#print axioms shifted_update
#print axioms primal_update
private theorem projected_det {p k : ℕ} (P : Block p d) (X : Block k d)
    (hp : (P * P.transpose).det ≠ 0) :
    (fromBlocks (P * P.transpose) (P * X.transpose)
      (X * P.transpose) (X * X.transpose)).det =
    (P * P.transpose).det * (projected P X * (projected P X).transpose).det := by
  let G := P * P.transpose
  let : Invertible G := G.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hp)
  have ei : inverse G = ⅟G := (invOf_eq_right_inv (inverse_right G hp)).symm
  rw [det_fromBlocks₁₁]
  congr 2
  let T := X * P.transpose * inverse G
  have orth := projected_orthogonal P X hp
  calc
    _ = projected P X * X.transpose := by
      change _ = (X - T * P) * X.transpose
      rw [Matrix.sub_mul]
      simp only [T, ei, Matrix.mul_assoc, G]
    _ = projected P X * (projected P X).transpose := by
      conv_rhs => rw [show projected P X = X - T * P from rfl, transpose_sub, transpose_mul]
      change _ = projected P X * (X.transpose - P.transpose * T.transpose)
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, orth, Matrix.zero_mul, sub_zero]

def firstRows (B : Matrix (Fin n) (Fin d) ℤ) (m : ℕ) (fit : m ≤ n) :
    Matrix (Fin m) (Fin d) ℤ := fun i ↦ B (i.castLE fit)

/-- Factor a full integer prefix Gram determinant at the start of a projected block. -/
private theorem factor_prefix (B : Matrix (Fin n) (Fin d) ℤ) (p k : ℕ)
    (fit : p+k ≤ n) (hp : gramDet (firstRows B p (by omega)) ≠ 0) :
    (gramDet (firstRows B (p+k) fit) : ℚ) =
    gramDet (firstRows B p (by omega)) *
      (blockAt B p k fit * (blockAt B p k fit).transpose).det := by
  let P := (firstRows B p (by omega)).map (Int.castRingHom ℚ)
  let X : Block k d := fun i u ↦ (B ⟨p+i.val,by omega⟩ u : ℚ)
  let M := (firstRows B (p+k) fit).map (Int.castRingHom ℚ)
  have castGram {m : ℕ} (R : Matrix (Fin m) (Fin d) ℤ) :
      (gramDet R : ℚ) = (R.map (Int.castRingHom ℚ) * (R.map (Int.castRingHom ℚ)).transpose).det := by
    change (Int.castRingHom ℚ) (R * R.transpose).det = _
    rw [RingHom.map_det]
    change ((R * R.transpose).map (Int.castRingHom ℚ)).det = _
    rw [Matrix.map_mul]; rfl
  have reg : (P * P.transpose).det ≠ 0 := by rw [← castGram]; exact_mod_cast hp
  rw [castGram, castGram]
  change (M * M.transpose).det = _
  rw [← det_submatrix_equiv_self finSumFinEquiv]
  have split : (M * M.transpose).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (P * P.transpose) (P * X.transpose) (X * P.transpose) (X * X.transpose) := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [split, projected_det P X reg]
  rfl

/-- A reciprocal row gives the principal Gram cofactor divided by the Gram determinant. -/
private theorem last_cofactor {k : ℕ} (A : Block (k+1) d) (c : Fin (k+1) → ℚ)
    (w : Fin d → ℚ) (rep : w = c ᵥ* A) (pair : A *ᵥ w = Pi.single (Fin.last k) 1) :
    (A * A.transpose).det * dotProduct w w =
      ((A * A.transpose).submatrix Fin.castSucc Fin.castSucc).det := by
  let l := Fin.last k
  let G := A * A.transpose
  have ww : dotProduct w w = c l := by
    conv_lhs => lhs; rw [rep]
    rw [← dotProduct_mulVec, pair, dotProduct_single, mul_one]
  have cg : c ᵥ* G = Pi.single l 1 := by
    rw [show G = A * A.transpose from rfl, ← vecMul_vecMul, ← rep, ← mulVec_transpose,
      transpose_transpose, pair]
  have e := congrArg (fun x ↦ (x ᵥ* G.adjugate) l) cg
  simp only [vecMul_vecMul, mul_adjugate, vecMul_smul, vecMul_one,
    Pi.smul_apply, smul_eq_mul, single_vecMul, one_mul] at e
  rw [ww]
  change G.det * c l = _
  rw [e]
  change G.adjugate l l = _
  rw [adjugate_fin_succ_eq_det_submatrix]
  simp [l, pow_add, ← mul_pow, G]

/-- Squared length of any last reciprocal row against the two adjacent flat prefixes. -/
theorem reciprocal_prefix (B : Matrix (Fin n) (Fin d) ℤ) (p k : ℕ)
    (fit : p+(k+1) ≤ n) (hp : gramDet (firstRows B p (by omega)) ≠ 0)
    (c : Fin (k+1) → ℚ) (w : Fin d → ℚ)
    (rep : w = c ᵥ* blockAt B p (k+1) fit)
    (pair : blockAt B p (k+1) fit *ᵥ w = Pi.single (Fin.last k) 1) :
    (gramDet (firstRows B (p+(k+1)) fit) : ℚ) * dotProduct w w =
      gramDet (firstRows B (p+k) (by omega)) := by
  rw [factor_prefix B p (k+1) fit hp, factor_prefix B p k _ hp, mul_assoc,
    last_cofactor _ c w rep pair]
  congr 2

#print axioms reciprocal_prefix
private theorem firstRows_pos (B : Matrix (Fin n) (Fin d) ℤ) (hb : LinearIndependent ℤ B)
    (m : ℕ) (fit : m ≤ n) : 0 < gramDet (firstRows B m fit) := by
  cases m with
  | zero => simp [gramDet]
  | succ j => exact gramDet_prefix_pos B hb ⟨j,fit⟩

theorem block_regular (B : Matrix (Fin n) (Fin d) ℤ) (hb : LinearIndependent ℤ B)
    (p k : ℕ) (fit : p+k ≤ n) :
    (blockAt B p k fit * (blockAt B p k fit).transpose).det ≠ 0 := by
  have e := factor_prefix B p k fit (firstRows_pos B hb p (by omega)).ne'
  intro h
  rw [h,mul_zero,Int.cast_eq_zero] at e
  exact (firstRows_pos B hb _ fit).ne' e

theorem reciprocal_normSq (B : Matrix (Fin n) (Fin d) ℤ) (hb : LinearIndependent ℤ B)
    (p k : ℕ) (fit : p+(k+1) ≤ n) (c : Fin (k+1) → ℚ) (w : Fin d → ℚ)
    (rep : w = c ᵥ* blockAt B p (k+1) fit)
    (pair : blockAt B p (k+1) fit *ᵥ w = Pi.single (Fin.last k) 1) :
    normSq B ⟨p+k, by omega⟩ * dotProduct w w = 1 := by
  let P : ℚ := gramDet (firstRows B (p+k) (by omega))
  have hP : 0 < P := by dsimp [P]; exact_mod_cast firstRows_pos B hb (p+k) (by omega)
  have e := reciprocal_prefix B p k fit (firstRows_pos B hb p (by omega)).ne' c w rep pair
  have factor : (gramDet (firstRows B (p+(k+1)) fit) : ℚ) =
      P * normSq B ⟨p+k,by omega⟩ := by
    change (gramDet (prefixRows B ⟨p+k,by omega⟩) : ℚ) = _
    rw [gramDet_prefix B, Fin.prod_univ_castSucc]
    have allPref (m : ℕ) (hm : m ≤ n) : (gramDet (firstRows B m hm) : ℚ) =
        ∏ i : Fin m, normSq B (i.castLE hm) := by
      cases m with
      | zero => simp [gramDet]
      | succ j => exact gramDet_prefix B ⟨j,hm⟩
    rw [show P = _ from allPref (p+k) (by omega)]
    rfl
  rw [factor,mul_assoc] at e
  exact mul_left_cancel₀ hP.ne' (e.trans (mul_one P).symm)

#print axioms block_regular
#print axioms reciprocal_normSq
private theorem changeAt_independent {k : ℕ} (p : ℕ) (fit : p+k ≤ n)
    (U V : Matrix (Fin k) (Fin k) ℤ) (inv : V * U = 1)
    (B : Matrix (Fin n) (Fin d) ℤ) (hb : LinearIndependent ℤ B) :
    LinearIndependent ℤ (changeAt p fit U B) := by
  let T := changeAt p fit U (1 : Matrix (Fin n) (Fin n) ℤ)
  let S := changeAt p fit V (1 : Matrix (Fin n) (Fin n) ℤ)
  have hi : S * T = 1 := by
    dsimp only [S,T]; rw [← flat_matrix, changeAt_undo p fit U V inv]
  rw [flat_matrix]
  apply Matrix.vecMul_injective_iff.mp
  intro a b h
  change a ᵥ* (T * B) = b ᵥ* (T * B) at h
  rw [← vecMul_vecMul, ← vecMul_vecMul] at h
  have e := congrArg (fun x ↦ x ᵥ* S) (Matrix.vecMul_injective_iff.mpr hb h)
  simpa only [vecMul_vecMul, mul_eq_one_comm.mp hi, vecMul_one] using e

private theorem repr_dual {k : ℕ} (A : Block k d) (z : Fin k → ℤ) :
    ∃ c : Fin k → ℚ, vector (dualRows A) z = c ᵥ* A := by
  unfold vector dualRows dual
  rw [transpose_mul, transpose_transpose, ← vecMul_vecMul]
  exact ⟨_,rfl⟩

private theorem single_last_pair {k : ℕ} (A : Block (k+1) d)
    (hr : (A * A.transpose).det ≠ 0) :
    A *ᵥ vector (dualRows A) (Pi.single (Fin.last k) 1) = Pi.single (Fin.last k) 1 := by
  rw [vector, ← mulVec_transpose, mulVec_mulVec, reciprocal_pairing A hr, one_mulVec]
  ext j; simp [Pi.single_apply,apply_ite]

private theorem dual_gain (B : Matrix (Fin n) (Fin d) ℤ) (hb : LinearIndependent ℤ B)
    (p k : ℕ) (fit : p+(k+1) ≤ n) (q : ℚ)
    (bad : let A := blockAt B p (k+1) fit
           let D := dualRows A
           q * weight D (dualSolveAt B p (k+1) fit (by omega)) <
             weight D (Pi.single (Fin.last k) 1)) :
    ∃ U V : Matrix (Fin (k+1)) (Fin (k+1)) ℤ, V * U = 1 ∧
      blockAt (changeAt p fit U B) p (k+1) fit *ᵥ
        vector (dualRows (blockAt B p (k+1) fit)) (dualSolveAt B p (k+1) fit (by omega)) =
        Pi.single (Fin.last k) 1 ∧
      q * normSq B ⟨p+k,by omega⟩ ≤ normSq (changeAt p fit U B) ⟨p+k,by omega⟩ := by
  let A := blockAt B p (k+1) fit
  let z := dualSolveAt B p (k+1) fit (by omega)
  let w := vector (dualRows A) z
  let old := vector (dualRows A) (Pi.single (Fin.last k) 1)
  have hr := block_regular B hb p (k+1) fit
  obtain ⟨U,V,inv,pair,_⟩ := shifted_update B p (k+1) fit (by omega) hr
  let C := changeAt p fit U B
  have hc := changeAt_independent p fit U V inv B hb
  obtain ⟨a,ha⟩ := repr_dual A z
  obtain ⟨b,hb'⟩ := repr_dual A (Pi.single (Fin.last k) 1)
  have rep : w = (a ᵥ* V.map (Int.castRingHom ℚ)) ᵥ* blockAt C p (k+1) fit := by
    rw [blockAt_changeAt, vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.map_mul, inv]
    simpa [w] using ha
  have hn := reciprocal_normSq C hc p k fit _ w rep pair
  have ho := reciprocal_normSq B hb p k fit b old hb' (single_last_pair A hr)
  have less : q * dotProduct w w < dotProduct old old := by
    simpa only [dotProduct,← sq, weight, w, old, A, z] using bad
  have positive (X : Rows n d) (j : Fin n) : 0 ≤ normSq X j := by
    unfold normSq LLL.Algorithm.dot
    exact Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
  let j : Fin n := ⟨p+k,by omega⟩
  have prod := mul_le_mul_of_nonneg_right less.le
    (mul_nonneg (positive B j) (positive C j))
  refine ⟨U,V,inv,pair,?_⟩
  change q * normSq B j ≤ normSq C j
  change normSq C j * dotProduct w w = 1 at hn
  change normSq B j * dotProduct old old = 1 at ho
  linear_combination (normSq C j) * ho - (q * normSq B j) * hn + prod

private theorem prefix_succ (B : Rows n d) (j : ℕ) (fit : j + 1 < n) :
    (gramDet (prefixRows B ⟨j+1, fit⟩) : ℚ) =
      gramDet (prefixRows B ⟨j, by omega⟩) * normSq B ⟨j+1,fit⟩ := by
  rw [gramDet_prefix, gramDet_prefix, Fin.prod_univ_castSucc]
  rfl

/-- The inverse squared-length ratio, with denominators cleared. -/
theorem boundary_ratio (B C : Rows n d) (j : ℕ) (fit : j + 1 < n)
    (same : gramDet (prefixRows C ⟨j+1,fit⟩) = gramDet (prefixRows B ⟨j+1,fit⟩)) :
    (gramDet (prefixRows C ⟨j, by omega⟩) : ℚ) * normSq C ⟨j+1,fit⟩ =
      gramDet (prefixRows B ⟨j, by omega⟩) * normSq B ⟨j+1,fit⟩ := by
  rw [← prefix_succ, ← prefix_succ, same]

theorem boundary_drop (B C : Rows n d) (hc : LinearIndependent ℤ C)
    (j : ℕ) (fit : j + 1 < n) (q : ℚ)
    (same : gramDet (prefixRows C ⟨j+1,fit⟩) = gramDet (prefixRows B ⟨j+1,fit⟩))
    (pos : 0 < normSq B ⟨j+1,fit⟩)
    (gain : q * normSq B ⟨j+1,fit⟩ ≤ normSq C ⟨j+1,fit⟩) :
    q * (gramDet (prefixRows C ⟨j, by omega⟩) : ℚ) ≤ gramDet (prefixRows B ⟨j, by omega⟩) := by
  apply le_of_mul_le_mul_right _ pos
  rw [← boundary_ratio B C j fit same, mul_right_comm q]
  conv_rhs => rw [mul_comm]
  apply mul_le_mul_of_nonneg_right gain
  exact_mod_cast (gramDet_prefix_pos C hc ⟨j, by omega⟩).le

/-- Boundary products in flat row order. Each index names the last included row. -/
noncomputable def flatPotential {r : ℕ} (B : Rows n d) (ends : Fin r → Fin n) : ℤ :=
  ∏ i, gramDet (prefixRows B (ends i))

theorem shifted_contract {r k : ℕ} (B : Matrix (Fin n) (Fin d) ℤ)
    (p : ℕ) (fit : p+k ≤ n) (U V : Matrix (Fin k) (Fin k) ℤ) (inv : V * U = 1)
    (ends : Fin r → Fin n) (i : Fin r) (edge : (ends i).val+2 = p+k)
    (outside : ∀ a, a ≠ i → (ends a).val < p ∨ p+k ≤ (ends a).val+1)
    (hb : LinearIndependent ℤ B) (q : ℚ)
    (gain : q * normSq B ⟨(ends i).val+1, by omega⟩ ≤
      normSq (changeAt p fit U B) ⟨(ends i).val+1, by omega⟩) :
    q * (flatPotential (changeAt p fit U B) ends : ℚ) ≤ flatPotential B ends := by
  let C := changeAt p fit U B
  let j := (ends i).val
  have fj : j+1 < n := by dsimp [j]; omega
  have same := changeAt_prefix p fit U V inv B ⟨j+1,fj⟩ (Or.inr (by dsimp [j]; omega))
  have ratio := boundary_ratio B C j fj same
  have positive : 0 < normSq B ⟨j+1,fj⟩ := by
    have hp : (0 : ℚ) < gramDet (prefixRows B ⟨j+1,fj⟩) := by
      exact_mod_cast gramDet_prefix_pos B hb _
    rw [prefix_succ B j fj] at hp
    exact pos_of_mul_pos_right hp (by exact_mod_cast (gramDet_prefix_pos B hb _).le)
  have positiveC : (0 : ℚ) < gramDet (prefixRows C (ends i)) := by
    have hp : (0 : ℚ) < gramDet (prefixRows C ⟨j+1,fj⟩) := by
      rw [same]; exact_mod_cast gramDet_prefix_pos B hb _
    rw [prefix_succ C j fj] at hp
    apply pos_of_mul_pos_left hp
    unfold normSq LLL.Algorithm.dot
    exact Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
  unfold flatPotential
  push_cast
  apply contract_boundary_product _ _ i
  · intro a
    exact_mod_cast (gramDet_prefix_pos B hb _).le
  · intro a ha
    exact_mod_cast changeAt_prefix p fit U V inv B (ends a) (outside a ha)
  · apply le_of_mul_le_mul_right _ positive
    change _ ≤ (gramDet (prefixRows B ⟨j,by dsimp [j]; omega⟩) : ℚ) * _
    rw [← ratio, mul_right_comm q]
    conv_rhs => rw [mul_comm]
    exact mul_le_mul_of_nonneg_right gain positiveC.le

private theorem primal_ok_after (B : Matrix (Fin n) (Fin d) ℤ) (hb : LinearIndependent ℤ B)
    (p k : ℕ) (fit : p+k ≤ n) (pos : 0 < k)
    (U V : Matrix (Fin k) (Fin k) ℤ) (inv : V * U = 1)
    (first : blockAt (changeAt p fit U B) p k fit ⟨0,pos⟩ =
        vector (blockAt B p k fit) (solveAt B p k fit pos)) :
    let C := changeAt p fit U B
    let A := blockAt C p k fit
    weight A (Pi.single ⟨0,pos⟩ 1) ≤ weight A (solveAt C p k fit pos) := by
  let C := changeAt p fit U B
  let A := blockAt B p k fit
  let D := blockAt C p k fit
  let z := solveAt C p k fit pos
  have hc := changeAt_independent p fit U V inv B hb
  have spec := solveAt_spec C p k fit pos (block_regular C hc _ _ fit)
  have castz : (fun i ↦ ((z ᵥ* U) i : ℚ)) = (fun i ↦ (z i : ℚ)) ᵥ* U.map (Int.castRingHom ℚ) := by
    ext j; simp [vecMul,dotProduct]
  have eq : vector D z = vector A (z ᵥ* U) := by
    unfold D C
    rw [blockAt_changeAt, vector, vector, castz, vecMul_vecMul]
  have nz := spec.1
  change vector D z ≠ 0 at nz
  rw [eq] at nz
  have shortest := (solveAt_spec B p k fit pos (block_regular B hb _ _ fit)).2 _ nz
  have row : vector D (Pi.single ⟨0,pos⟩ 1) = D ⟨0,pos⟩ := by
    unfold vector
    have castOne : (fun i : Fin k ↦ (((Pi.single ⟨0,pos⟩ 1 : Fin k → ℤ) i) : ℚ)) =
        Pi.single ⟨0,pos⟩ (1 : ℚ) := by ext i; simp [Pi.single_apply,apply_ite]
    rw [castOne, single_vecMul,one_smul]; rfl
  change weight D _ ≤ weight D z
  unfold weight at shortest ⊢
  change D ⟨0,pos⟩ = _ at first
  rw [row, eq, first]
  exact shortest

private theorem blockAt_before {s k : ℕ} (p u : ℕ) (fit : p+s ≤ n) (earlier : u+k ≤ p)
    (U : Matrix (Fin s) (Fin s) ℤ) (B : Matrix (Fin n) (Fin d) ℤ) :
    blockAt (changeAt p fit U B) u k (by omega) = blockAt B u k (by omega) := by
  unfold blockAt
  congr 1
  · ext i j
    have h : ¬ p ≤ i.val := by omega
    simp [changeAt,h]
  · ext i j
    have h : ¬ p ≤ u+i.val := by omega
    simp [changeAt,h]

section Pass
variable {b k : ℕ} (pos : 0 < b)
private abbrev Flat (b k d : ℕ) := Matrix (Fin (k*b)) (Fin d) ℤ
def boundaryEnds (pos : 0 < b) (i : Fin (k-1)) : Fin (k*b) :=
  ⟨(i.val+1)*b-1, by
    have h := Nat.mul_le_mul_right b (show i.val+1 ≤ k by omega)
    have hp : 0 < (i.val+1)*b := Nat.mul_pos (by omega) pos
    omega⟩

private theorem fitAt (i : Fin k) : i.val*b+b ≤ k*b := by
  simpa [Nat.succ_mul] using Nat.mul_le_mul_right b i.isLt

private def primalOK (B : Flat b k d) (i : Fin k) : Prop :=
  let A := blockAt B (i.val*b) b (fitAt i)
  weight A (Pi.single ⟨0,pos⟩ 1) ≤ weight A (solveAt B _ _ (fitAt i) pos)

/-- A left-to-right sweep of actual unimodular shortest-vector insertions. -/
private inductive Sweep (pos : 0 < b) (B : Flat b k d) : ℕ → Flat b k d → Prop
  | start : Sweep pos B 0 B
  | step {m : ℕ} {D : Flat b k d} (prev : Sweep pos B m D) (fit : m*b+b ≤ k*b)
      (U V : Matrix (Fin b) (Fin b) ℤ) (inv : V*U = 1)
      (row : blockAt (changeAt (m*b) fit U D) (m*b) b fit ⟨0,pos⟩ =
        vector (blockAt D (m*b) b fit) (solveAt D (m*b) b fit pos)) :
      Sweep pos B (m+1) (changeAt (m*b) fit U D)

private theorem normalize (B : Flat b k d) (hb : LinearIndependent ℤ B)
    (m : ℕ) (hm : m ≤ k) : ∃ C : Flat b k d, Sweep pos B m C ∧ LinearIndependent ℤ C ∧ lattice C = lattice B ∧
      flatPotential C (boundaryEnds pos) = flatPotential B (boundaryEnds pos) ∧
      ∀ i : Fin k, i.val < m → primalOK pos C i := by
  induction m with
  | zero => exact ⟨B,.start,hb,rfl,rfl,by omega⟩
  | succ m ih =>
    obtain ⟨D,prevSweep,hd,lat,pot,ok⟩ := ih (by omega)
    let j : Fin k := ⟨m,hm⟩
    have fit := fitAt (b := b) j
    obtain ⟨U,V,inv,row⟩ := primal_update D (m*b) b fit pos (block_regular D hd _ _ fit)
    let C := changeAt (m*b) fit U D
    refine ⟨C,.step prevSweep fit U V inv row,changeAt_independent _ fit U V inv D hd,
      (changeAt_preserves _ fit U V inv D).trans lat,?_,?_⟩
    · rw [← pot]
      apply Finset.prod_congr rfl
      intro a _
      apply changeAt_prefix _ fit U V inv
      change (a.val+1)*b-1 < m*b ∨ m*b+b ≤ (a.val+1)*b-1+1
      have hp : 0 < (a.val+1)*b := Nat.mul_pos (by omega) pos
      by_cases h : a.val+1 ≤ m
      · exact Or.inl (by have := Nat.mul_le_mul_right b h; omega)
      · right
        have le := Nat.mul_le_mul_right b (show m+1 ≤ a.val+1 by omega)
        rw [Nat.succ_mul] at le
        omega
    · intro i hi
      by_cases h : i.val = m
      · have e : i = j := Fin.ext h
        subst i
        exact primal_ok_after D hd _ _ fit pos U V inv row
      · have prev := ok i (by omega)
        have le := Nat.mul_le_mul_right b (show i.val+1 ≤ m by omega)
        rw [Nat.succ_mul] at le
        unfold primalOK solveAt at prev ⊢
        simpa only [C, blockAt_before (m*b) (i.val*b) fit le U D] using prev

abbrev SlideBasis (b k d : ℕ) := {B : Matrix (Fin (k*b)) (Fin d) ℤ // LinearIndependent ℤ B}

private def passRows (q : ℚ) (B : Flat b k d) (C : Flat b k d) (clean : Bool) : Prop :=
  ∃ D, Sweep pos B k D ∧
    if clean then C = D else
      ∃ (i : Fin (k-1)) (fit : i.val*b+1+b ≤ k*b) (U V : Matrix (Fin b) (Fin b) ℤ),
        let p := i.val*b+1
        let w := vector (dualRows (blockAt D p b fit)) (dualSolveAt D p b fit pos)
        V*U = 1 ∧ C = changeAt p fit U D ∧
          blockAt C p b fit *ᵥ w = Pi.single ⟨b-1,by omega⟩ 1 ∧
          q * weight (dualRows (blockAt D p b fit)) (dualSolveAt D p b fit pos) <
            weight (dualRows (blockAt D p b fit)) (Pi.single ⟨b-1,by omega⟩ 1)

private def passSpec (q : ℚ) (B : SlideBasis b k d) (out : SlideBasis b k d × Bool) : Prop :=
  passRows pos q B.val out.1.val out.2 ∧ lattice out.1.val = lattice B.val ∧
  (out.2 = true → slideCheck out.1.val pos q = true) ∧
  (out.2 = false → q * (flatPotential out.1.val (boundaryEnds pos) : ℚ) ≤
    flatPotential B.val (boundaryEnds pos))

private theorem exists_pass (q : ℚ) (B : SlideBasis b k d) :
    ∃ out, passSpec pos q B out := by
  classical
  cases b with
  | zero => omega
  | succ t =>
    let β := t+1
    obtain ⟨D,sweep,hd,lat,pot,normalized⟩ := normalize pos B.val B.property k le_rfl
    by_cases clean : slideCheck D pos q = true
    · exact ⟨(⟨D,hd⟩,true),⟨D,sweep,rfl⟩,lat,fun _ ↦ clean,by simp⟩
    have primal : ∀ i : Fin k, primalOK pos D i := fun i ↦ normalized i i.isLt
    simp only [slideCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      forall_const, decide_eq_true_eq] at clean
    obtain ⟨i, bad⟩ := Classical.not_forall.mp (fun rest ↦ clean ⟨primal,rest⟩)
    let p := i.val*β+1
    have fit : p+β ≤ k*β := by
      have h := Nat.mul_le_mul_right β (show i.val+2 ≤ k by omega)
      dsimp [p]; rw [Nat.add_mul] at h; dsimp [β] at *; omega
    obtain ⟨U,V,inv,pair,gain⟩ := dual_gain D hd p t fit q (lt_of_not_ge bad)
    let C := changeAt p fit U D
    refine ⟨(⟨C,changeAt_independent _ fit U V inv D hd⟩,false),
      ⟨D,sweep,i,fit,U,V,inv,rfl,pair,lt_of_not_ge bad⟩,
      (changeAt_preserves _ fit U V inv D).trans lat,by simp, fun _ ↦ ?_⟩
    change q * (flatPotential C (boundaryEnds pos) : ℚ) ≤ flatPotential B.val _
    rw [← pot]
    have idx (a : Fin (k-1)) : (boundaryEnds pos a).val+1 = (a.val+1)*β := by
      change (a.val+1)*β-1+1 = _
      have hp : 0 < (a.val+1)*β := Nat.mul_pos (by omega) pos
      omega
    have edge : (boundaryEnds pos i).val+2 = p+β := by
      have h := idx i; rw [Nat.succ_mul] at h; dsimp [p]; omega
    apply shifted_contract D p fit U V inv (boundaryEnds pos) i edge _ hd q
    · have h : (boundaryEnds pos i).val+1 = p+t := by dsimp [β] at edge; omega
      simpa only [h] using gain
    · intro a ha
      rcases lt_or_gt_of_ne (show a.val ≠ i.val from fun e ↦ ha (Fin.ext e)) with h | h
      · left
        have le := Nat.mul_le_mul_right β (show a.val+1 ≤ i.val by omega)
        have := idx a; dsimp [p]; omega
      · right
        have le := Nat.mul_lt_mul_of_pos_right (show i.val+1 < a.val+1 by omega) pos
        change (i.val+1)*β < (a.val+1)*β at le
        rw [Nat.succ_mul i.val] at le
        rw [idx]
        dsimp only [p]; omega

/-- One noncomputable pass, chosen from the verified primal sweep and shifted dual update. -/
noncomputable def slidePass (q : ℚ) (B : SlideBasis b k d) : SlideBasis b k d × Bool :=
  (exists_pass pos q B).choose

/-- The concrete pass terminates within any fuel satisfying the boundary-product bound. -/
theorem slide_reduce (q : ℚ) (hq : 1 < q) (B : SlideBasis b k d) (fuel : ℕ)
    (enough : (flatPotential B.val (boundaryEnds pos) : ℚ) < q ^ fuel) :
    let out := slideLoop (slidePass pos q) fuel B
    out.2 = true ∧ lattice out.1.val = lattice B.val ∧ slideCheck out.1.val pos q = true := by
  let pass := slidePass (k := k) (d := d) pos q
  have spec (X : SlideBasis b k d) : passSpec pos q X (pass X) := (exists_pass pos q X).choose_spec
  have clean := slideLoop_fuel pass (fun X ↦ flatPotential X.val (boundaryEnds pos)) q hq
    (fun X ↦ Finset.prod_pos fun i _ ↦ gramDet_prefix_pos _ X.property _) (fun X ↦ (spec X).2.2.2)
    fuel B enough
  exact ⟨clean,slideLoop_preserves pass (fun X ↦ lattice X.val) (fun X ↦ (spec X).2.1) fuel B,
    slideLoop_clean pass (fun X ↦ slideCheck X.val pos q = true) (fun X ↦ (spec X).2.2.1)
      fuel B clean⟩

/-- Least natural fuel satisfying the geometric bound. -/
def slideFuel (q : ℚ) (hq : 1 < q) (P : ℤ) : ℕ :=
  Nat.find (pow_unbounded_of_one_lt (P : ℚ) hq)

private theorem slideFuel_spec (q : ℚ) (hq : 1 < q) (P : ℤ) :
    (P : ℚ) < q ^ slideFuel q hq P := Nat.find_spec (pow_unbounded_of_one_lt (P : ℚ) hq)

theorem slide_reduce_eps (ε : ℚ) (he : 0 < ε) (B : SlideBasis b k d) :
    let q := (1+ε)^2
    let fuel := slideFuel q (by dsimp [q]; nlinarith [sq_nonneg ε])
      (flatPotential B.val (boundaryEnds pos))
    let out := slideLoop (slidePass pos q) fuel B
    out.2 = true ∧ lattice out.1.val = lattice B.val ∧ slideCheck out.1.val pos q = true := by
  apply slide_reduce
  · nlinarith [sq_nonneg ε]
  · exact slideFuel_spec _ _ _

#print axioms slide_reduce_eps
#print axioms slidePass
#print axioms slide_reduce
end Pass
#print axioms shifted_contract
#print axioms dualSolveAt_primitive
#print axioms boundary_ratio
#print axioms boundary_drop
end SigabaNeo.Slide

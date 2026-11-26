module

public import Definitions.Def_LatticeAttack_Reduction_Slide_Approx
public import Definitions.Def_LatticeAttack_Reduction_BKZ_Hermite
import all Definitions.Def_LatticeAttack_Reduction_Slide_Update
import all Definitions.Def_LatticeAttack_Reduction_Slide_Approx
public import Definitions.Def_LatticeAttack_Reduction_LLL_Bridge

set_option autoImplicit true

public section

namespace SigabaNeo.Slide

open Matrix Module
open scoped MatrixOrder

private theorem gram_weight {k d : ℕ} (M : Matrix (Fin k) (Fin d) ℝ) (z : Fin k → ℝ) :
    ∑ j, (z ᵥ* M) j ^ 2 = z ⬝ᵥ ((M * M.transpose) *ᵥ z) := by
  rw [← mulVec_vecMul, dotProduct_mulVec]
  simp [dotProduct, sq]

/-- Minkowski witness in integer coefficients for any regular rectangular rational block.
A square real factor of the Gram matrix preserves all coefficient-vector lengths. -/
theorem hermite_weight {k d : ℕ} [NeZero k] (A : Block k d)
    (h : (A * A.transpose).det ≠ 0) :
    ∃ z : Fin k → ℤ, z ≠ 0 ∧ (weight A z : ℝ) ≤
      ((k : ℝ) + 4) / Real.pi * ((A * A.transpose).det : ℝ) ^ (1 / (k : ℝ)) := by
  classical
  let M := A.map (Rat.castHom ℝ)
  have hd : (M * M.transpose).det = ((A * A.transpose).det : ℝ) := by
    change _ = (Rat.castHom ℝ) _
    rw [RingHom.map_det]
    change _ = ((A * A.transpose).map (Rat.castHom ℝ)).det
    rw [Matrix.map_mul]
    rfl
  have hp := (posSemidef_self_mul_conjTranspose M).nonneg
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hp
  let T := X.transpose
  have hg : M * M.transpose = T * T.transpose := by simpa [T, Matrix.star_eq_conjTranspose] using hX
  have he : ((A * A.transpose).det : ℝ) = T.det ^ 2 := by
    simp only [← hd, hg, det_mul, det_transpose, sq]
  have ht : T.det ≠ 0 := by
    intro hz
    have hn : ((A * A.transpose).det : ℝ) ≠ 0 := by exact_mod_cast h
    exact hn (by simp [he, hz])
  let b := basisOfLinearIndependentOfCardEqFinrank' T.row
    (T.linearIndependent_rows_of_det_ne_zero ht) (by simp)
  have eb : ⇑b = T.row := coe_basisOfLinearIndependentOfCardEqFinrank' ..
  let L := Submodule.span ℤ (Set.range b)
  have hc : ZLattice.covolume L = |T.det| := by
    rw [ZLattice.covolume_eq_det _ (b.restrictScalars ℤ)]
    congr 2
    ext i j
    change ((b.restrictScalars ℤ i).val) j = _
    rw [Basis.restrictScalars_apply, eb]
    rfl
  obtain ⟨v,hv,bound⟩ := BKZ.hermite_linear_coords L
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp v.property
  refine ⟨z, ?_, ?_⟩
  · rintro rfl
    exact hv (Subtype.ext (by simpa using hz.symm))
  let w := fun i ↦ (z i : ℝ)
  have ev : v.val = w ᵥ* T := by
    ext j
    rw [← hz]
    simp [Finset.sum_apply, eb, vecMul, dotProduct, w, Matrix.row, mul_comm]
  have ew : (weight A z : ℝ) = ∑ j, (w ᵥ* M) j ^ 2 := by
    simp [weight, vector, vecMul, dotProduct, M, w, Matrix.map_apply]
  rw [ew, gram_weight, hg, ← gram_weight, ← ev]
  rw [hc] at bound
  convert bound using 2
  rw [he, ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  push_cast
  ring

open LLL.Algorithm

/-- Gram determinant of the projected block as a product of squared GSO lengths. -/
theorem blockAt_det {n d : ℕ} (B : Rows n d) (hb : LinearIndependent ℤ B)
    (p k : ℕ) (fit : p+k ≤ n) :
    (blockAt B p k fit * (blockAt B p k fit).transpose).det =
      ∏ j : Fin k, normSq B ⟨p+j.val, by omega⟩ := by
  have pref (m : ℕ) (hm : m ≤ n) : (gramDet (firstRows B m hm) : ℚ) =
      ∏ j : Fin m, normSq B (j.castLE hm) := by
    cases m with
    | zero => simp [gramDet]
    | succ j => exact gramDet_prefix B ⟨j,hm⟩
  have hp := firstRows_pos B hb p (by omega)
  have h := factor_prefix B p k fit hp.ne'
  have hn : (gramDet (firstRows B p (by omega)) : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  apply mul_left_cancel₀ hn
  rw [← h, pref, Fin.prod_univ_add, pref]
  rfl

theorem dualRows_det {k d : ℕ} (A : Block k d) (h : (A * A.transpose).det ≠ 0) :
    (dualRows A * (dualRows A).transpose).det = (A * A.transpose).det⁻¹ := by
  have e : dualRows A = (inverse (A * A.transpose)).transpose * A := by
    rw [dualRows, dual, transpose_mul, transpose_transpose]
  nth_rw 1 [e]
  rw [Matrix.mul_assoc, reciprocal_pairing _ h, Matrix.mul_one, det_transpose]
  have eq := congrArg Matrix.det (inverse_right _ h)
  rw [det_mul, det_one] at eq
  field_simp
  linear_combination eq

/-- Simultaneous witnesses for a primal and reciprocal block, in squared GSO units. -/
theorem blockAt_hermite {n d k : ℕ} [NeZero k] (B : Rows n d) (hb : LinearIndependent ℤ B)
    (p : ℕ) (fit : p+k ≤ n) :
    let A := blockAt B p k fit
    let V := ((∏ j : Fin k, normSq B ⟨p+j.val, by omega⟩ : ℚ) : ℝ)
    ∃ x y : Fin k → ℤ, x ≠ 0 ∧ y ≠ 0 ∧
      (weight A x : ℝ) ≤ ((k:ℝ)+4)/Real.pi * V^(1/(k:ℝ)) ∧
      (weight (dualRows A) y : ℝ) ≤ ((k:ℝ)+4)/Real.pi * V⁻¹^(1/(k:ℝ)) := by
  intro A V
  have hr := block_regular B hb p k fit
  obtain ⟨x,hx,wx⟩ := hermite_weight A hr
  obtain ⟨y,hy,wy⟩ := hermite_weight (dualRows A) (dualGram_regular _ hr)
  rw [dualRows_det _ hr] at wy
  exact ⟨x,y,hx,hy, by simpa [A,V,blockAt_det B hb] using wx,
    by simpa [A,V,blockAt_det B hb] using wy⟩


/-- The common factors of the two overlapping Gram determinants cancel. -/
private theorem overlap {n d k : ℕ} (B : Rows n d) (hb : LinearIndependent ℤ B)
    (p : ℕ) (fit : p+1+(k+1) ≤ n) :
    let A := blockAt B p (k+1) (by omega)
    let S := blockAt B (p+1) (k+1) fit
    (A * A.transpose).det * normSq B ⟨p+(k+1),by omega⟩ =
      (S * S.transpose).det * normSq B ⟨p,by omega⟩ := by
  dsimp only
  rw [blockAt_det B hb, blockAt_det B hb, Fin.prod_univ_succ, Fin.prod_univ_castSucc]
  simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
  simp only [Nat.add_assoc, Nat.add_comm 1]
  ring

/-- Logarithmic ratio of successive checked block heads, in squared-length units. -/
theorem checked_log_boundary {k b d : ℕ} (B : Rows (k*(b+1)) d) (hb : LinearIndependent ℤ B)
    {q : ℚ} (hq : 0 < q) (ok : slideCheck B (by omega) q = true)
    (i : Fin (k-1)) (fit : i.val*(b+1)+1+(b+1) ≤ k*(b+1)) :
    let p := i.val*(b+1)
    let r := (normSq B ⟨p,by dsimp [p]; omega⟩ : ℝ)
    let s := (normSq B ⟨p+(b+1),by dsimp [p]; omega⟩ : ℝ)
    (b:ℝ)*(Real.log r - Real.log s) ≤
      ((b:ℝ)+1)*(2*Real.log (((b:ℝ)+1+4)/Real.pi) + Real.log q) := by
  intro p r s
  let A := blockAt B p (b+1) (by omega)
  let S := blockAt B (p+1) (b+1) fit
  let U := ((A * A.transpose).det : ℝ)
  let V := ((S * S.transpose).det : ℝ)
  let C := ((b:ℝ)+1+4)/Real.pi
  have reg := block_regular B hb (p+1) (b+1) fit
  obtain ⟨x,hx,wx⟩ := hermite_weight A (block_regular B hb _ _ _)
  obtain ⟨y,hy,wy⟩ := hermite_weight (dualRows S) (dualGram_regular _ reg)
  rw [dualRows_det _ reg, Rat.cast_inv] at wy
  simp only [Nat.cast_add, Nat.cast_one] at wx wy
  have base := checked_boundary B hb hq.le ok i x y hx hy fit
  have bnd : r ≤ (weight A x : ℝ) * ((q:ℝ) * weight (dualRows S) y) * s := by
    dsimp only [r,s]
    exact_mod_cast base
  have ns (j : Fin (k*(b+1))) : 0 < normSq B j := by
    have := block_regular B hb j.val 1 (by omega)
    rw [blockAt_det B hb] at this
    have hn : normSq B j ≠ 0 := by simpa using this
    apply lt_of_le_of_ne _ hn.symm
    unfold normSq LLL.Algorithm.dot
    exact Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
  have hr : 0 < r := by dsimp only [r]; exact_mod_cast ns _
  have hs : 0 < s := by dsimp only [s]; exact_mod_cast ns _
  have hU : 0 < U := by dsimp [U,A]; rw [blockAt_det B hb]; exact_mod_cast Finset.prod_pos (fun _ _ ↦ ns _)
  have hV : 0 < V := by dsimp [V,S]; rw [blockAt_det B hb]; exact_mod_cast Finset.prod_pos (fun _ _ ↦ ns _)
  have hc : 0 < C := by dsimp [C]; positivity
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hov : U*s = V*r := by dsimp only [U,V,s,r]; exact_mod_cast overlap B hb p fit
  have hl := congrArg Real.log hov
  rw [Real.log_mul hU.ne' hs.ne', Real.log_mul hV.ne' hr.ne'] at hl
  have big : r ≤ C * U^(1/((b:ℝ)+1)) * ((q:ℝ) * (C * V⁻¹^(1/((b:ℝ)+1)))) * s := by
    apply bnd.trans
    gcongr
    · apply mul_nonneg hq'.le
      exact_mod_cast (Finset.sum_nonneg fun j _ ↦ sq_nonneg (vector (dualRows S) y j) : 0 ≤ weight (dualRows S) y)
  have H := Real.log_le_log hr big
  repeat rw [Real.log_mul (by positivity) (by positivity)] at H
  rw [Real.log_rpow hU, Real.log_rpow (inv_pos.mpr hV), Real.log_inv] at H
  have hβ : 0 < (b:ℝ)+1 := by positivity
  field_simp [hβ.ne'] at H
  change _ ≤ _ * (2 * Real.log C + _)
  nlinarith

/-- Squared-length factor per block boundary, iterated over m boundaries. -/
noncomputable def slideSqFactor (b m : ℕ) (q : ℚ) : ℝ :=
  Real.exp ((m:ℝ)*((b:ℝ)+1)*(2*Real.log (((b:ℝ)+1+4)/Real.pi) + Real.log q)/b)

theorem checked_head_factor {k b d : ℕ} (B : Rows (k*(b+1)) d) (hb : LinearIndependent ℤ B)
    (hbpos : 0 < b) {q : ℚ} (hq : 0 < q) (ok : slideCheck B (by omega) q = true)
    (m : ℕ) (hm : m < k) :
    (normSq B ⟨0,Nat.mul_pos (by omega) (by omega)⟩ : ℝ) ≤ slideSqFactor b m q *
      (normSq B ⟨m*(b+1),Nat.mul_lt_mul_of_pos_right hm (by omega)⟩ : ℝ) := by
  have hk : 0 < k := by omega
  let head (j : ℕ) := (normSq B ⟨j*(b+1) % (k*(b+1)), Nat.mod_lt _ (by positivity)⟩ : ℝ)
  have idx (j : ℕ) (hj : j < k) : j*(b+1) % (k*(b+1)) = j*(b+1) :=
    Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_right hj (by omega))
  have tel := mordell_log_telescope (fun j ↦ Real.log (head j)) m ((b:ℝ)+1)
    (Real.log (((b:ℝ)+1+4)/Real.pi)) (Real.log q) (by
      intro j hj
      have hh : j+2 ≤ k := by omega
      have h := Nat.mul_le_mul_right (b+1) hh
      rw [Nat.add_mul] at h
      have step := checked_log_boundary B hb hq ok ⟨j,by omega⟩ (by dsimp; omega)
      simp only [head,idx j (by omega),idx (j+1) (by omega),add_sub_cancel_right]
      simpa [Nat.succ_mul] using step)
  have pos (j : ℕ) : 0 < head j := by
    let t : Fin (k*(b+1)) := ⟨_,Nat.mod_lt (j*(b+1)) (by positivity)⟩
    have hn := block_regular B hb t.val 1 (by omega)
    rw [blockAt_det B hb] at hn
    have hn' : normSq B t ≠ 0 := by simpa using hn
    have hnn : 0 ≤ normSq B t := by
      unfold normSq LLL.Algorithm.dot
      exact Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
    change 0 < (normSq B t : ℝ)
    exact_mod_cast (lt_of_le_of_ne hnn hn'.symm : 0 < normSq B t)
  have br : (0:ℝ) < b := by exact_mod_cast hbpos
  have hh : Real.log (head 0) - Real.log (head m) ≤
      (m:ℝ)*((b:ℝ)+1)*(2*Real.log (((b:ℝ)+1+4)/Real.pi) + Real.log q)/b := by
    apply (le_div_iff₀ br).2
    linarith
  have H := Real.exp_le_exp.mpr hh
  rw [Real.exp_sub, Real.exp_log (pos _), Real.exp_log (pos _)] at H
  simpa [head,idx m hm,slideSqFactor] using (div_le_iff₀ (pos m)).mp H

private theorem sum_split {n p β : ℕ} (f : Fin n → ℚ) (fit : p+β ≤ n)
    (tail : ∀ j : Fin n, p+β ≤ j.val → f j = 0) :
    ∑ j, f j = (∑ j : Fin p, f ⟨j.val,by omega⟩) +
      ∑ j : Fin β, f ⟨p+j.val,by omega⟩ := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le fit
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  have hz (j : Fin t) : f (Fin.natAdd (p+β) j) = 0 := tail _ (by simp)
  simp only [hz,Finset.sum_const_zero,add_zero]
  rfl

/-- Projecting away the prefix can only shorten a vector supported through this block. -/
theorem block_weight_le {n d β : ℕ} (B : Rows n d) (hb : LinearIndependent ℤ B)
    (p : ℕ) (fit : p+β ≤ n) (z : Fin n → ℤ) (tail : ∀ j : Fin n, p+β ≤ j.val → z j = 0) :
    weight (blockAt B p β fit) (fun j ↦ z ⟨p+j.val,by omega⟩) ≤
      weight (Matrix.map B (Int.castRingHom ℚ)) z := by
  let P := (firstRows B p (by omega)).map (Int.castRingHom ℚ)
  let X : Block β d := fun i j ↦ (B ⟨p+i.val,by omega⟩ j : ℚ)
  let a : Fin p → ℚ := fun i ↦ (z ⟨i.val,by omega⟩ : ℚ)
  let c : Fin β → ℚ := fun i ↦ (z ⟨p+i.val,by omega⟩ : ℚ)
  let Y := projected P X
  let t := a + c ᵥ* (X * P.transpose * inverse (P * P.transpose))
  have hp : (P * P.transpose).det ≠ 0 := by
    have h := (firstRows_pos B hb p (by omega)).ne'
    have he : ((gramDet (firstRows B p (by omega))) : ℚ) = (P * P.transpose).det := by
      change (Int.castRingHom ℚ) _ = _
      unfold gramDet
      rw [RingHom.map_det]
      change (((firstRows B p (by omega)) * (firstRows B p (by omega)).transpose).map (Int.castRingHom ℚ)).det = _
      rw [Matrix.map_mul]; rfl
    rw [← he]; exact_mod_cast h
  have hz : vector (Matrix.map B (Int.castRingHom ℚ)) z = a ᵥ* P + c ᵥ* X := by
    ext j
    apply sum_split (fun i ↦ (z i : ℚ) * (B i j : ℚ)) fit
    intro i hi
    simp [tail i hi]
  have split : vector (Matrix.map B (Int.castRingHom ℚ)) z = c ᵥ* Y + t ᵥ* P := by
    rw [hz]
    simp only [Y, projected, t, vecMul_sub, add_vecMul, vecMul_vecMul]
    abel
  have orth : (c ᵥ* Y) ⬝ᵥ (t ᵥ* P) = 0 := by
    rw [← dotProduct_mulVec, mulVec_vecMul, projected_orthogonal P X hp, zero_mulVec,
      dotProduct_zero]
  change (∑ j, (c ᵥ* Y) j ^ 2) ≤ _
  rw [weight,split]
  have sqsum (v : Fin d → ℚ) : (∑ j, v j ^ 2) = v ⬝ᵥ v := by simp [dotProduct,sq]
  rw [sqsum,sqsum,add_dotProduct,dotProduct_add,dotProduct_add,orth,dotProduct_comm (t ᵥ* P),orth]
  have nn : 0 ≤ (t ᵥ* P) ⬝ᵥ (t ᵥ* P) := Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
  linarith

/-- Uniform approximation against every nonzero integer coefficient vector. -/
theorem checked_approx_sq {k b d : ℕ} (B : Rows (k*(b+1)) d) (hb : LinearIndependent ℤ B)
    (hk : 0 < k) (hbpos : 0 < b) {q : ℚ} (hq : 1 ≤ q) (ok : slideCheck B (by omega) q = true)
    (z : Fin (k*(b+1)) → ℤ) (hz : z ≠ 0) :
    (normSq B ⟨0,by positivity⟩ : ℝ) ≤ slideSqFactor b (k-1) q *
      (weight (Matrix.map B (Int.castRingHom ℚ)) z : ℝ) := by
  classical
  let I := Finset.univ.filter (fun j ↦ z j ≠ 0)
  have hi : I.Nonempty := by
    by_contra h
    apply hz
    ext j
    by_contra hn
    exact h ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩⟩
  let l := I.max' hi
  let m := l.val / (b+1)
  let p := m*(b+1)
  have hm : m < k := (Nat.div_lt_iff_lt_mul (by omega)).2 l.isLt
  have fit : p+(b+1) ≤ k*(b+1) := by
    simpa [p,Nat.succ_mul] using Nat.mul_le_mul_right (b+1) (show m+1 ≤ k by omega)
  have idx : p+l.val%(b+1) = l.val := by simpa [p,m,Nat.mul_comm] using Nat.div_add_mod l.val (b+1)
  let x : Fin (b+1) → ℤ := fun j ↦ z ⟨p+j.val,by omega⟩
  have hx : x ≠ 0 := by
    intro h
    have h0 := congrFun h (⟨l.val%(b+1),Nat.mod_lt _ (by omega)⟩ : Fin (b+1))
    have hl := (Finset.mem_filter.mp (I.max'_mem hi)).2
    exact hl (by simpa [x,idx] using h0)
  have reg := block_regular B hb p (b+1) fit
  have prim := slideCheck_primal B (by omega) ok ⟨m,hm⟩ fit x reg (vector_ne_zero _ reg x hx)
  rw [first_weight B hb] at prim
  have short := block_weight_le B hb p fit z (by
    intro j hj
    by_contra hn
    have hle : j ≤ l := Finset.le_max' I j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
    change j.val ≤ l.val at hle
    have := Nat.mod_lt l.val (show 0 < b+1 by omega)
    omega)
  have hW : (normSq B ⟨p,by omega⟩ : ℝ) ≤ (weight (Matrix.map B (Int.castRingHom ℚ)) z : ℝ) := by
    exact_mod_cast prim.trans short
  have F := checked_head_factor B hb hbpos (lt_of_lt_of_le zero_lt_one hq) ok m hm
  have mono : slideSqFactor b m q ≤ slideSqFactor b (k-1) q := by
    have hc : 1 ≤ ((b:ℝ)+1+4)/Real.pi := (le_div_iff₀ Real.pi_pos).2 (by linarith [Real.pi_lt_four, Nat.cast_nonneg (α := ℝ) b])
    have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
    have hlog := Real.log_nonneg hc
    have hlogq := Real.log_nonneg hq'
    unfold slideSqFactor
    gcongr
    omega
  exact F.trans ((mul_le_mul_of_nonneg_left hW (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_right mono (by
      exact_mod_cast (Finset.sum_nonneg fun j _ ↦ sq_nonneg (vector (Matrix.map B (Int.castRingHom ℚ)) z j) :
        0 ≤ weight (Matrix.map B (Int.castRingHom ℚ)) z))))

/-- First-vector guarantee for every nonzero point in the integer span. The exponent
in the length factor is half the squared-length exponent. -/
theorem checked_approx {k b d : ℕ} [NeZero (k*(b+1))] (B : Rows (k*(b+1)) d)
    (hb : LinearIndependent ℤ B) (hk : 0 < k) (hbpos : 0 < b) {q : ℚ} (hq : 1 ≤ q)
    (ok : slideCheck B (by omega) q = true)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ Submodule.span ℤ (Set.range (realRows B)))
    (hne : v ≠ 0) :
    ‖realRows B 0‖ ≤ Real.sqrt (slideSqFactor b (k-1) q) * ‖v‖ := by
  obtain ⟨z,hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
  have hz' : z ≠ 0 := by rintro rfl; exact hne (by simpa using hz.symm)
  have H := checked_approx_sq B hb hk hbpos hq ok z hz'
  have hrow : starRow B 0 = rationalRow B 0 := by
    rw [starRow]
    simp only [sub_eq_self]
    apply Finset.sum_eq_zero
    intro j _
    have := j.isLt
    simp at this
  have hfirst : (normSq B 0 : ℝ) = ‖realRows B 0‖^2 := by
    rw [normSq,hrow,EuclideanSpace.real_norm_sq_eq]
    simp [realRows, realVec, LLL.Algorithm.dot, sq]
  have hvec (u : Fin d) : (v u : ℝ) = (vector (Matrix.map B (Int.castRingHom ℚ)) z u : ℝ) := by
    rw [← hz]
    simp [realRows,realVec,rationalRow,vector,vecMul,dotProduct,WithLp.ofLp_sum,
      ← Int.cast_smul_eq_zsmul ℝ]
    change (∑ x, (z x : ℝ) * (B x u : ℝ)) = ∑ x, (z x : ℝ) * ((B x u : ℚ) : ℝ)
    simp
  have hw : ‖v‖^2 = (weight (Matrix.map B (Int.castRingHom ℚ)) z : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [hvec, weight,Rat.cast_sum,Rat.cast_pow]
  change (normSq B 0 : ℝ) ≤ _ at H
  rw [hfirst,← hw] at H
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rwa [mul_pow,Real.sq_sqrt (show 0 ≤ slideSqFactor b (k-1) q from (Real.exp_pos _).le)]

/-- Length factor for the tolerance used by slide_reduce_eps, for block size b+1. -/
theorem slideFactor_eps (b m : ℕ) (ε : ℚ) (he : 0 ≤ ε) :
    Real.sqrt (slideSqFactor b m ((1+ε)^2)) =
      ((1+(ε:ℝ))*(((b:ℝ)+1+4)/Real.pi)) ^ ((m:ℝ)*((b:ℝ)+1)/b) := by
  have he' : 0 ≤ (ε:ℝ) := by exact_mod_cast he
  have hp : 0 < 1+(ε:ℝ) := by positivity
  have hc : 0 < ((b:ℝ)+1+4)/Real.pi := by positivity
  rw [Real.rpow_def_of_pos (mul_pos hp hc), Real.log_mul hp.ne' hc.ne',
    slideSqFactor, ← Real.exp_half]
  push_cast
  rw [Real.log_pow]
  congr 1
  ring

/-- Global covolume bound for a square checked basis, with the dimension-n
Minkowski ball radius and the slide approximation factor. -/
theorem checked_covolume {k b : ℕ} [NeZero (k*(b+1))] (B : Rows (k*(b+1)) (k*(b+1)))
    (hb : LinearIndependent ℤ B) (hk : 0 < k) (hbpos : 0 < b) {q : ℚ} (hq : 1 ≤ q)
    (ok : slideCheck B (by omega) q = true) :
    let n := k*(b+1)
    let L := Submodule.span ℤ (Set.range (realRows B))
    ‖realRows B 0‖ ≤ Real.sqrt (slideSqFactor b (k-1) q) *
      (2 * (ZLattice.covolume L /
        (Real.sqrt Real.pi ^ n / Real.Gamma ((n:ℝ)/2+1))) ^ (1/(n:ℝ))) := by
  let a := basisOfLinearIndependentOfCardEqFinrank' (realRows B) (realRows_independent B hb)
    (by simp)
  have ea : ⇑a = realRows B := coe_basisOfLinearIndependentOfCardEqFinrank' ..
  obtain ⟨v,hv,hbound⟩ := BKZ.hermite_ball (Submodule.span ℤ (Set.range a))
  have hm : v.val ∈ Submodule.span ℤ (Set.range (realRows B)) := by
    rw [← ea]; exact v.property
  have hne : v.val ≠ 0 := fun h ↦ hv (Subtype.ext h)
  dsimp only
  nth_rw 2 [← ea]
  exact (checked_approx B hb hk hbpos hq ok _ hm hne).trans
    (mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _))

/-- Gap consequence for a square embedded lattice checked by slide reduction. -/
theorem checked_unique_shortest {k b : ℕ} [NeZero (k*(b+1))] (B : Rows (k*(b+1)) (k*(b+1)))
    (hb : LinearIndependent ℤ B) (hk : 0 < k) (hbpos : 0 < b) {q : ℚ} (hq : 1 ≤ q)
    (ok : slideCheck B (by omega) q = true) {u : EuclideanSpace ℝ (Fin (k*(b+1)))}
    (hu : u ∈ Submodule.span ℤ (Set.range (realRows B))) (hne : u ≠ 0)
    (gap : ∀ w ∈ Submodule.span ℤ (Set.range (realRows B)), w ∉ Submodule.span ℤ {u} →
      Real.sqrt (slideSqFactor b (k-1) q) * ‖u‖ < ‖w‖) :
    realRows B 0 ∈ Submodule.span ℤ {u} :=
  LLL.unique_shortest_of_approx _ (checked_approx B hb hk hbpos hq ok) hu hne gap

#print axioms blockAt_hermite
#print axioms checked_covolume
#print axioms checked_unique_shortest
end SigabaNeo.Slide

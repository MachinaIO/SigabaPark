module

public import Mathlib

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.LLL.Algorithm

abbrev Rows (n d : ℕ) := Fin n → Fin d → ℤ

variable {n d : ℕ}

def lattice (B : Rows n d) := Submodule.span ℤ (Set.range B)

def dot (v w : Fin d → ℚ) := ∑ a, v a * w a

def rationalRow (B : Rows n d) (i : Fin n) : Fin d → ℚ := fun a ↦ B i a

/-- Classical Gram–Schmidt with exact rational projections. -/
def starRow (B : Rows n d) (i : Fin n) : Fin d → ℚ :=
  let x := rationalRow B i
  x - ∑ j : Fin i.val,
    let y := starRow B ⟨j.val, lt_trans j.isLt i.isLt⟩
    (dot x y / dot y y) • y
termination_by i.val
decreasing_by exact j.isLt

def normSq (B : Rows n d) (i : Fin n) := dot (starRow B i) (starRow B i)

def mu (B : Rows n d) (i j : Fin n) := dot (rationalRow B i) (starRow B j) / normSq B j

def lovasz (B : Rows n d) (i j : Fin n) : Prop :=
  3 / 4 * normSq B j ≤ normSq B i + mu B i j ^ 2 * normSq B j

instance (B : Rows n d) (i j : Fin n) : Decidable (lovasz B i j) := by
  unfold lovasz
  infer_instance

def Reduced (B : Rows n d) : Prop :=
  (∀ i j, j < i → |mu B i j| ≤ 1 / 2) ∧ (∀ i j, j.val + 1 = i.val → lovasz B i j)

def shear (B : Rows n d) (i j : Fin n) (z : ℤ) : Rows n d :=
  Function.update B i (B i - z • B j)

private theorem row_mem (B : Rows n d) (i : Fin n) : B i ∈ lattice B :=
  Submodule.subset_span ⟨i, rfl⟩

private theorem shear_le (B : Rows n d) (i j : Fin n) (z : ℤ) :
    lattice (shear B i j z) ≤ lattice B := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  by_cases h : k = i
  · subst k
    simpa [shear] using (lattice B).sub_mem (row_mem B i) ((lattice B).smul_mem z (row_mem B j))
  · simpa [shear, h] using row_mem B k

theorem lattice_shear (B : Rows n d) (i j : Fin n) (h : j < i) (z : ℤ) :
    lattice (shear B i j z) = lattice B := by
  apply le_antisymm (shear_le ..)
  have inv : shear (shear B i j z) i j (-z) = B := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [shear, h.ne]
    · simp [shear, hk]
  simpa only [inv] using shear_le (shear B i j z) i j (-z)

def swapRows (B : Rows n d) (i j : Fin n) : Rows n d := B ∘ Equiv.swap i j

theorem lattice_swap (B : Rows n d) (i j : Fin n) : lattice (swapRows B i j) = lattice B := by
  simp [lattice, swapRows, Set.range_comp]

def pairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i ↦ (List.finRange n).reverse.map fun j ↦ (i, j)

theorem mem_pairs (i j : Fin n) : (i,j) ∈ pairs n := by simp [pairs]

/-- Every fuel unit permits one elementary operation. Normal exit is also checked at zero fuel. -/
structure Result (B : Rows n d) where
  rows : Rows n d
  swaps : ℕ
  normal : Bool
  span_eq : lattice rows = lattice B
  reduced : normal = true → Reduced rows

def run (fuel : ℕ) (B : Rows n d) : Result B :=
  let badSize := fun p : Fin n × Fin n ↦ decide (p.2 < p.1 ∧ 1 / 2 < |mu B p.1 p.2|)
  let badSwap := fun p : Fin n × Fin n ↦ decide (p.2.val + 1 = p.1.val ∧ ¬ lovasz B p.1 p.2)
  match hs : (pairs n).find? badSize with
  | some p =>
    have hb : badSize p = true := List.find?_some hs
    have hp : p.2 < p.1 := (of_decide_eq_true (show decide (_ ∧ _) = true from hb)).1
    let z := round (mu B p.1 p.2)
    match fuel with
    | 0 => ⟨B, 0, false, rfl, by simp⟩
    | f+1 =>
      let r := run f (shear B p.1 p.2 z)
      ⟨r.rows, r.swaps, r.normal, r.span_eq.trans (lattice_shear B _ _ hp z), r.reduced⟩
  | none =>
    match hw : (pairs n).find? badSwap with
    | some p =>
      match fuel with
      | 0 => ⟨B, 0, false, rfl, by simp⟩
      | f+1 =>
        let r := run f (swapRows B p.1 p.2)
        ⟨r.rows, r.swaps + 1, r.normal, r.span_eq.trans (lattice_swap B _ _), r.reduced⟩
    | none => ⟨B, 0, true, rfl, by
        intro _
        constructor
        · intro i j h
          have := List.find?_eq_none.mp hs (i,j) (mem_pairs i j)
          simpa [badSize, h] using this
        · intro i j h
          have := List.find?_eq_none.mp hw (i,j) (mem_pairs i j)
          simpa [badSwap, h] using this⟩

theorem run_lattice (fuel : ℕ) (B : Rows n d) : lattice (run fuel B).rows = lattice B :=
  (run fuel B).span_eq

theorem run_reduced (fuel : ℕ) (B : Rows n d) (h : (run fuel B).normal = true) :
    Reduced (run fuel B).rows := (run fuel B).reduced h

open Matrix

def prefixRows (B : Rows n d) (k : Fin n) : Matrix (Fin (k.val + 1)) (Fin d) ℤ :=
  fun i ↦ B (i.castLE k.isLt)

noncomputable def gramDet {m : ℕ} (A : Matrix (Fin m) (Fin d) ℤ) : ℤ :=
  (A * A.transpose).det

noncomputable def potential (B : Rows n d) : ℤ := ∏ k, gramDet (prefixRows B k)

theorem gramDet_prefix_pos (B : Rows n d) (h : LinearIndependent ℤ B) (k : Fin n) :
    0 < gramDet (prefixRows B k) := by
  let A := prefixRows B k
  have hi : LinearIndependent ℤ A.row :=
    h.comp _ (Fin.castLE_injective k.isLt)
  apply Matrix.PosDef.det_pos
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simp [Matrix.IsHermitian]
  · intro x hx
    change 0 < dotProduct (star x) ((A * A.transpose).mulVec x)
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    have hn : A.vecMul x ≠ 0 := fun hz ↦ hx ((Matrix.vecMul_injective_iff.mpr hi)
      (hz.trans (Matrix.zero_vecMul A).symm))
    simpa using Matrix.dotProduct_star_self_pos_iff.mpr hn

theorem potential_one_le (B : Rows n d) (h : LinearIndependent ℤ B) : 1 ≤ potential B := by
  suffices 0 < potential B by omega
  apply Finset.prod_pos
  intro k _
  exact gramDet_prefix_pos B h k

theorem potential_shear (B : Rows n d) (i j : Fin n) (h : j < i) (z : ℤ) :
    potential (shear B i j z) = potential B := by
  apply Finset.prod_congr rfl
  intro k _
  by_cases hi : i.val < k.val + 1
  · let u : Fin (k.val + 1) := ⟨i.val, hi⟩
    let v : Fin (k.val + 1) := ⟨j.val, lt_trans h hi⟩
    have huv : u ≠ v := fun he ↦ h.ne' (Fin.ext (congrArg (Fin.val (n := k.val + 1)) he))
    let T := Matrix.transvection u v (-z)
    have eqn : prefixRows (shear B i j z) k = T * prefixRows B k := by
      ext a b
      by_cases ha : a = u
      · subst a
        simp [T, prefixRows, shear, u, v, sub_eq_add_neg]
      · have hn : a.castLE k.isLt ≠ i := fun he ↦ ha (Fin.ext (congrArg (Fin.val (n := n)) he))
        simp [T, Matrix.transvection_mul_apply_of_ne _ _ _ _ ha, prefixRows, shear, hn]
    unfold gramDet
    rw [eqn, Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc T]
    simp [Matrix.det_mul, T,
      Matrix.det_transvection_of_ne _ _ huv]
  · have eqn : prefixRows (shear B i j z) k = prefixRows B k := by
      funext a
      have hn : a.castLE k.isLt ≠ i := fun he ↦ hi (congrArg Fin.val he ▸ a.isLt)
      simp [prefixRows, shear, hn]
    rw [eqn]

/-- Only the prefix ending at the lower of the two swapped indices can change volume. -/
theorem gramDet_swap_of_ne (B : Rows n d) (i j k : Fin n) (adj : j.val + 1 = i.val)
    (hk : k ≠ j) :
    gramDet (prefixRows (swapRows B i j) k) = gramDet (prefixRows B k) := by
  by_cases hi : i.val ≤ k.val
  · let u : Fin (k.val + 1) := ⟨i.val, by omega⟩
    let v : Fin (k.val + 1) := ⟨j.val, by omega⟩
    let e := Equiv.swap u v
    let A := prefixRows B k
    have eqn : prefixRows (swapRows B i j) k = A.submatrix e id := by
      ext a b
      by_cases hu : a = u
      · subst a
        simp [prefixRows, swapRows, A, e, u, v]
      by_cases hv : a = v
      · subst a
        simp [prefixRows, swapRows, A, e, u, v]
      have hu' : a.castLE k.isLt ≠ i := fun he ↦ hu (Fin.ext (congrArg (Fin.val (n := n)) he))
      have hv' : a.castLE k.isLt ≠ j := fun he ↦ hv (Fin.ext (congrArg (Fin.val (n := n)) he))
      simp [prefixRows, swapRows, A, e, Equiv.swap_apply_of_ne_of_ne, hu, hv, hu', hv']
    rw [eqn]
    apply Matrix.det_submatrix_equiv_self e (A * A.transpose)
  · have hkj : k.val ≠ j.val := fun h ↦ hk (Fin.ext h)
    have eqn : prefixRows (swapRows B i j) k = prefixRows B k := by
      funext a
      have hi' : a.castLE k.isLt ≠ i := by intro h; have := congrArg Fin.val h; simp at this; omega
      have hj' : a.castLE k.isLt ≠ j := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [prefixRows, swapRows, Equiv.swap_apply_of_ne_of_ne hi' hj']
    rw [eqn]

#print axioms gramDet_swap_of_ne

/- Remaining obligations for the iteration bound: identify the affected prefix Gram determinant
with the corresponding rational Gram–Schmidt product, derive strict contraction on a failed
Lovász test, and bound the number of elementary size reductions between swaps. -/

#print axioms potential_one_le
#print axioms potential_shear
#print axioms run_lattice
#print axioms run_reduced

end SigabaNeo.LLL.Algorithm

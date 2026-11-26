module

public import Definitions.Def_LatticeAttack_Reduction_Slide_Tour
public import Mathlib.Data.Matrix.Block

set_option autoImplicit true

public section
namespace SigabaNeo.Slide
open Matrix
variable {k β d : ℕ}

/-- The second row index selects a block, the first its offset. -/
abbrev BlockRows (k β d : ℕ) := Matrix (Fin β × Fin k) (Fin d) ℤ

def boundaryRows (B : BlockRows k β d) (m : ℕ) (hm : m ≤ k) : BlockRows m β d :=
  fun i ↦ B (i.1, i.2.castLE hm)

def changeBlocks (U : Fin k → Matrix (Fin β) (Fin β) ℤ) (B : BlockRows k β d) :
    BlockRows k β d := fun (i,b) j ↦ ∑ a, U b i a * B (a,b) j

theorem boundary_change (U : Fin k → Matrix (Fin β) (Fin β) ℤ) (B : BlockRows k β d)
    (m : ℕ) (hm : m ≤ k) :
    boundaryRows (changeBlocks U B) m hm =
      blockDiagonal (fun b : Fin m ↦ U (b.castLE hm)) * boundaryRows B m hm := by
  ext ⟨i,b⟩ j
  simp [boundaryRows, changeBlocks, Matrix.mul_apply, Fintype.sum_prod_type,
    blockDiagonal_apply, ite_mul]

private theorem span_mul_le {ι : Type*} [Fintype ι] (T : Matrix ι ι ℤ)
    (A : Matrix ι (Fin d) ℤ) :
    Submodule.span ℤ (Set.range (T * A)) ≤ Submodule.span ℤ (Set.range A) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  apply (Submodule.mem_span_range_iff_exists_fun ℤ).mpr
  refine ⟨T i, ?_⟩
  ext j
  simp [Matrix.mul_apply, Finset.sum_apply]

/-- Simultaneous unimodular changes in disjoint blocks preserve every whole-block prefix. -/
theorem boundary_invariant (U V : Fin k → Matrix (Fin β) (Fin β) ℤ)
    (inv : ∀ i, V i * U i = 1) (B : BlockRows k β d) (m : ℕ) (hm : m ≤ k) :
    let A := boundaryRows B m hm
    let C := boundaryRows (changeBlocks U B) m hm
    Submodule.span ℤ (Set.range C) = Submodule.span ℤ (Set.range A) ∧
      (C * C.transpose).det = (A * A.transpose).det := by
  dsimp only
  rw [boundary_change]
  let T := blockDiagonal (fun b : Fin m ↦ U (b.castLE hm))
  let S := blockDiagonal (fun b : Fin m ↦ V (b.castLE hm))
  let A := boundaryRows B m hm
  have hi : S * T = 1 := by
    simp only [S, T, ← blockDiagonal_mul, inv]
    exact blockDiagonal_one
  have hd := congrArg Matrix.det hi
  simp only [det_mul, det_one] at hd
  have sq : T.det * T.det = 1 := by
    have hu := Int.isUnit_iff.mp (isUnit_iff_dvd_one.mpr ⟨S.det, by rw [mul_comm]; exact hd.symm⟩)
    rcases hu with h | h <;> simp [h]
  constructor
  · apply le_antisymm (span_mul_le T A)
    simpa only [← Matrix.mul_assoc, hi, Matrix.one_mul] using span_mul_le S (T * A)
  · change ((T * A) * (T * A).transpose).det = _
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc A, det_mul, det_mul, det_transpose]
    linear_combination (A * A.transpose).det * sq

/-- Product over the nonempty proper block boundaries. -/
noncomputable def boundaryPotential (B : BlockRows k β d) : ℤ :=
  ∏ i : Fin (k - 1), let A := boundaryRows B (i.val + 1) (by omega)
                     (A * A.transpose).det

theorem boundaryPotential_invariant (U V : Fin k → Matrix (Fin β) (Fin β) ℤ)
    (inv : ∀ i, V i * U i = 1) (B : BlockRows k β d) :
    boundaryPotential (changeBlocks U B) = boundaryPotential B := by
  apply Finset.prod_congr rfl
  exact fun i _ ↦ (boundary_invariant U V inv B _ _).2

theorem boundaryPotential_pos (B : BlockRows k β d) (hi : LinearIndependent ℤ B) :
    0 < boundaryPotential B := by
  apply Finset.prod_pos
  intro i _
  let A := boundaryRows B (i.val + 1) (by omega)
  have ind : LinearIndependent ℤ A.row := by
    apply hi.comp (fun j : Fin β × Fin (i.val + 1) ↦
      (j.1, j.2.castLE (show i.val + 1 ≤ k by omega)))
    rintro ⟨a,b⟩ ⟨c,e⟩ eq
    simpa using eq
  apply Matrix.PosDef.det_pos
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simp [Matrix.IsHermitian]
  · intro x hx
    change 0 < dotProduct (star x) ((A * A.transpose).mulVec x)
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    have hn : A.vecMul x ≠ 0 := fun hz ↦ hx ((Matrix.vecMul_injective_iff.mpr ind)
      (hz.trans (Matrix.zero_vecMul A).symm))
    simpa using Matrix.dotProduct_star_self_pos_iff.mpr hn

/-- One improving boundary contracts the entire product by the same factor. -/
theorem contract_boundary_product {r : ℕ} (before after : Fin r → ℚ) (j : Fin r) (q : ℚ)
    (nonneg : ∀ i, 0 ≤ before i) (same : ∀ i, i ≠ j → after i = before i)
    (drop : q * after j ≤ before j) : q * ∏ i, after i ≤ ∏ i, before i := by
  have rest : ∏ i ∈ Finset.univ.erase j, after i = ∏ i ∈ Finset.univ.erase j, before i :=
    Finset.prod_congr rfl fun i hi ↦ same i (Finset.mem_erase.mp hi).1
  rw [← Finset.mul_prod_erase Finset.univ after (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ before (Finset.mem_univ j), rest, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right drop (Finset.prod_nonneg fun i _ ↦ nonneg i)

end SigabaNeo.Slide

module

public import Definitions.Def_LatticeAttack_Reduction_Slide_SVP
public import Definitions.Def_LatticeAttack_Reduction_LLL_Algorithm

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Slide

variable {n d : ℕ} (B : Matrix (Fin n) (Fin d) ℤ) (β : ℕ) (hβ : 0 < β) (δ : ℚ)

/-- Test a projected block against its first projected row. -/
def needsInsertion (i : Fin (n - 1)) : Bool :=
  let k := min β (n - i.val)
  have fit : i.val + k ≤ n := by dsimp [k]; omega
  have pos : 0 < k := by dsimp [k]; omega
  let A := blockAt B i.val k fit
  decide (weight A (solveAt B i.val k fit pos) < δ * weight A (Pi.single ⟨0, pos⟩ 1))

/-- Scan all eligible positions in order, stopping at the first failed block. -/
def firstInsertion : Option (Fin (n - 1)) :=
  (List.finRange (n - 1)).find? (needsInsertion B β hβ δ)

/-- A clean scan certifies the relaxed inequality for every nonzero projected vector. -/
theorem clean_block_bound (clean : firstInsertion B β hβ δ = none) (i : Fin (n - 1)) :
    let k := min β (n - i.val)
    have fit : i.val + k ≤ n := by dsimp [k]; omega
    have pos : 0 < k := by dsimp [k]; omega
    let A := blockAt B i.val k fit
    (A * A.transpose).det ≠ 0 → ∀ z : Fin k → ℤ, vector A z ≠ 0 →
      δ * weight A (Pi.single ⟨0, pos⟩ 1) ≤ weight A z := by
  dsimp only
  intro hr z hz
  have neg := List.find?_eq_none.mp clean i (by simp)
  simp only [needsInsertion, decide_eq_true_eq] at neg
  exact (le_of_not_gt neg).trans ((solveAt_spec B _ _ _ _ hr).2 z hz)

/-- Every common integer factor of the exact solver's coefficients is a unit. -/
theorem solveAt_primitive (p k : ℕ) (fit : p + k ≤ n) (pos : 0 < k)
    (hr : ((blockAt B p k fit) * (blockAt B p k fit).transpose).det ≠ 0)
    (t : ℤ) (z : Fin k → ℤ) (factor : solveAt B p k fit pos = fun i ↦ t * z i) :
    t = 1 ∨ t = -1 := by
  let A := blockAt B p k fit
  obtain ⟨nz, best⟩ := solveAt_spec B p k fit pos hr
  have scale : vector A (solveAt B p k fit pos) = (t : ℚ) • vector A z := by
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
  have h := best z nv
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

private theorem lattice_mul_le (U : Matrix (Fin n) (Fin n) ℤ) :
    LLL.Algorithm.lattice (U * B) ≤ LLL.Algorithm.lattice B := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  apply (Submodule.mem_span_range_iff_exists_fun ℤ).mpr
  refine ⟨U i, ?_⟩
  ext j
  simp [Matrix.mul_apply, Finset.sum_apply]

/-- An integral completion with integral left inverse preserves the row lattice. -/
theorem lattice_completion (U V : Matrix (Fin n) (Fin n) ℤ) (inv : V * U = 1) :
    LLL.Algorithm.lattice (U * B) = LLL.Algorithm.lattice B := by
  apply le_antisymm (lattice_mul_le B U)
  simpa only [← Matrix.mul_assoc, inv, Matrix.one_mul] using lattice_mul_le (U * B) V

/-- For diag(2,3,1), the unique shortest direction is the last row. With that row
first, a unimodular completion has signed minor a*y-b*x = ±1, while its
two-row Gram determinant is 4*a²+9*b². The original two-row determinant was 36. -/
theorem completion_changes_prefix (a b x y : ℤ)
    (unitMinor : a*y-b*x = 1 ∨ a*y-b*x = -1) : 4*a^2 + 9*b^2 ≠ 36 := by
  intro eq
  have al : -3 ≤ a := by nlinarith [sq_nonneg b, sq_nonneg (a+4)]
  have au : a ≤ 3 := by nlinarith [sq_nonneg b, sq_nonneg (a-4)]
  have bl : -2 ≤ b := by nlinarith [sq_nonneg a, sq_nonneg (b+3)]
  have bu : b ≤ 2 := by nlinarith [sq_nonneg a, sq_nonneg (b-3)]
  interval_cases a <;> interval_cases b <;> norm_num at * <;> omega

#print axioms clean_block_bound
#print axioms solveAt_primitive
#print axioms lattice_completion
#print axioms completion_changes_prefix

end SigabaNeo.Slide

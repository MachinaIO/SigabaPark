module

public import Definitions.Def_LatticeAttack_Attacks_Primal_Planted
import all Definitions.Def_LatticeAttack_Attacks_Primal_Planted
public import Definitions.Def_LatticeAttack_Reduction_LLL_Termination
public import Definitions.Def_LatticeAttack_QAry_Basis

set_option autoImplicit true

/-!
# The LLL primal attack on LWE, end to end

From the public `(A, b)` build the explicit integer basis `QAry.rows A b` of the embedding
lattice (`QAry/Basis.lean`), run LLL with the proven fuel `fuelBound` (it exits normally,
`run_normal_of_fuel`, after at most `log_{4/3}` of the potential swaps, `run_swap_bound`) and read
the first row. `lll_attack`: if `2^((d−1)/2)·‖(e,s,1)‖ < R` and `A ∉ badMatrices q e s R`
(probability `≤ ((R + √d/2)/G)^d` over uniform `A`, `Planted.badMatrices_probability`), the first
row is `±(e, s, 1)`.

The gap condition `2^((d−1)/2)·‖(e,s,1)‖ < R ≲ G` only holds in small dimension; this is a
proven close variant of the primal uSVP attack, not the estimator's BKZ-based cost.
-/

public section

namespace SigabaNeo.LLL

open SigabaNeo.Planted SigabaNeo.LLL.Algorithm

variable {m n q : ℕ} [Fact q.Prime]

/-- Integer vectors as real vectors. -/
noncomputable def intVec {d : ℕ} : (Fin d → ℤ) →ₗ[ℤ] EuclideanSpace ℝ (Fin d) where
  toFun x := WithLp.toLp 2 fun a ↦ (x a : ℝ)
  map_add' x y := by ext; simp
  map_smul' z x := by ext; simp

theorem realRows_eq {d k : ℕ} (B : Rows k d) (i : Fin k) : realRows B i = intVec (B i) := by
  ext a; simp [realRows, realVec, rationalRow, intVec]

theorem span_realRows {d k : ℕ} (B : Rows k d) :
    Submodule.span ℤ (Set.range (realRows B)) = (lattice B).map intVec := by
  rw [lattice, Submodule.map_span, ← Set.range_comp]
  congr 2

theorem intVec_eq_embed (w : Fin (dim m n) → ℤ) :
    intVec w = embed (w ∘ QAry.indexEquiv) := by
  ext a
  simp [intVec, embed, QAry.indexEquiv]

/-- **The LLL primal attack.** -/
theorem lll_attack [NeZero (dim m n)] (A : Matrix (Fin m) (Fin n) (ZMod q))
    (e : Fin m → ℤ) (s : Fin n → ℤ) {R : ℝ} (hR : 0 ≤ R)
    (hγ : (2 : ℝ) ^ ((((dim m n : ℕ) : ℝ) - 1) / 2) * ‖embed (plantedPoint e s)‖ < R)
    (hA : A ∉ badMatrices q e s R) :
    let B := QAry.rows A (fun i ↦ A i ⬝ᵥ (fun j ↦ (s j : ZMod q)) + e i)
    realRows (run (fuelBound B) B).rows 0 = embed (plantedPoint e s) ∨
      realRows (run (fuelBound B) B).rows 0 = -embed (plantedPoint e s) := by
  intro B
  have hB : LinearIndependent ℤ B := QAry.rows_independent _ _
  set B' := (run (fuelBound B) B).rows
  have hs := run_real_span (fuelBound B) B
  have hb : LinearIndependent ℝ (realRows B') := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank _ (by simp)
    rw [← Submodule.span_span_of_tower ℤ ℝ, hs, Submodule.span_span_of_tower,
      (realRows_independent B hB).span_eq_top_of_card_eq_finrank' (by simp)]
  refine reduced_finds_planted A e s (realRows B') hb ?_ ?_ hR hγ hA
  · intro v
    rw [hs, span_realRows, Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w ∘ QAry.indexEquiv, ?_, intVec_eq_embed w⟩
      have := (QAry.rows_span_iff_member _ _ w).mp hw
      exact (QAry.member_planted A e s _).mp this
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z ∘ QAry.indexEquiv.symm, ?_, ?_⟩
      · apply (QAry.rows_span_iff_member _ _ _).mpr
        change QAry.Member _ _ ((z ∘ QAry.indexEquiv.symm) ∘ QAry.indexEquiv)
        rw [(QAry.member_planted A e s _)]
        simpa [Function.comp_def] using hz
      · rw [intVec_eq_embed]; simp [Function.comp_def]
  · intro v hv hne
    exact run_approx B hB v (hs ▸ hv) hne

end SigabaNeo.LLL

#print axioms SigabaNeo.LLL.lll_attack

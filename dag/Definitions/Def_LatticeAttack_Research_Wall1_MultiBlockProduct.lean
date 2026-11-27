module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit true

/-! # Independence of disjoint coordinate blocks (PROOF_GAP Wall 1, Parts 131/132)

A finite product law on `ι → Y`, with one weight `w` on `Y` summing to one, makes functions of
pairwise disjoint coordinate blocks independent: the expectation of a product of block functions
is the product of the block expectations, each computed under the product law on its own block. -/

public section
namespace SigabaNeo.Wall1.MultiBlock

/-- Expectation, under the product law with coordinate weight `w`, of `G` on `κ → Y`. -/
@[expose] def expect {Y κ : Type*} [Fintype Y] [Fintype κ] [DecidableEq κ] (w : Y → ℚ)
    (G : (κ → Y) → ℚ) : ℚ :=
  ∑ x : κ → Y, (∏ j, w (x j)) * G x

/-- Disjoint blocks: the expectation of a product of functions of disjoint coordinate blocks
equals the product of their expectations. Here `b i : Fin (r i) → ι` lists the coordinates of
block `i`, and injectivity of the combined map says the blocks are disjoint and repetition-free. -/
theorem block_product {Y ι K : Type*} [Fintype Y] [Fintype ι] [DecidableEq ι] [Fintype K]
    [DecidableEq K] {r : K → ℕ} (b : ∀ i, Fin (r i) → ι)
    (hb : Function.Injective (fun p : (Σ i, Fin (r i)) ↦ b p.1 p.2))
    (w : Y → ℚ) (hw : ∑ y, w y = 1) (G : ∀ i, (Fin (r i) → Y) → ℚ) :
    expect w (fun x : ι → Y ↦ ∏ i, G i (fun a ↦ x (b i a))) =
      ∏ i, expect w (G i) := by
  classical
  unfold expect
  let β := fun p : (Σ i, Fin (r i)) ↦ b p.1 p.2
  let R := {j : ι // j ∉ Set.range β}
  let E : (Σ i, Fin (r i)) ⊕ R ≃ ι :=
    (Equiv.sumCongr (Equiv.ofInjective β hb) (Equiv.refl R)).trans
      (Equiv.sumCompl (· ∈ Set.range β))
  have hE (p) : E.symm (b p.1 p.2) = .inl p := by
    apply E.injective
    simp only [Equiv.apply_symm_apply]
    rfl
  rw [← (E.arrowCongr (Equiv.refl Y)).sum_comp,
    ← (Equiv.sumArrowEquivProdArrow _ _ _).symm.sum_comp, Fintype.sum_prod_type]
  have step (f : (Σ i, Fin (r i)) → Y) (g : R → Y) :
      (∏ j, w ((E.arrowCongr (Equiv.refl Y)) ((Equiv.sumArrowEquivProdArrow _ _ _).symm (f, g)) j)) *
        ∏ i, G i (fun a ↦ (E.arrowCongr (Equiv.refl Y))
          ((Equiv.sumArrowEquivProdArrow _ _ _).symm (f, g)) (b i a)) =
      ((∏ p, w (f p)) * ∏ i, G i (fun a ↦ f ⟨i, a⟩)) * ∏ j, w (g j) := by
    rw [mul_right_comm]
    congr 1
    · rw [← E.prod_comp, Fintype.prod_sum_type]
      simp [Equiv.arrowCongr_apply, Equiv.sumArrowEquivProdArrow]
    · refine Finset.prod_congr rfl fun i _ ↦ congrArg (G i) (funext fun a ↦ ?_)
      simp only [Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_apply]
      rw [hE ⟨i, a⟩]
      rfl
  simp_rw [step, ← Finset.mul_sum]
  have hR : ∑ g : R → Y, ∏ j, w (g j) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : R) y ↦ w y), hw, Finset.prod_const_one]
  simp_rw [hR, mul_one]
  rw [← (Equiv.piCurry fun _ _ ↦ Y).symm.sum_comp, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [Fintype.prod_sigma, ← Finset.prod_mul_distrib]
  rfl

end SigabaNeo.Wall1.MultiBlock

#print axioms SigabaNeo.Wall1.MultiBlock.block_product

import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder3Reindex

set_option autoImplicit true

noncomputable section
namespace SigabaNeo.Rogers.AllOrders
open PlaneParam

variable {n r k q : ℕ} (A : Diagram r k (q+1)) (x : Fin r → Fin n → ℤ)

theorem pivot_independent (hx : LinearIndependent ℤ x) :
    LinearIndependent ℤ (fun i ↦ expand A x (A.pivot i)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let B := diagramBasisMatrix A
  have hd : B.det.natAbs = Nat.card (rowImage A) := diagramKernelBasis_det A
  have hinj := Matrix.mulVec_injective_of_det_ne_zero (M := B.transpose)
    (by rw [Matrix.det_transpose]; intro h; exact Nat.card_pos.ne' (hd.symm.trans (by simp [h])))
  have h : ∑ a, (B.transpose.mulVec c a) • x a = 0 := by
    funext l
    have hh := congrFun hc l
    simp only [expand, diagramIntegerEntry_pivot, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, Finset.mul_sum, ← mul_assoc] at hh
    rw [Finset.sum_comm] at hh
    simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Pi.zero_apply, mul_comm (B _ _), B] using hh
  have h0 := funext (Fintype.linearIndependent_iff.mp hx _ h)
  have he : c = 0 := hinj (by rw [Matrix.mulVec_zero]; exact h0)
  simp [he]

theorem expand_ne_zero (hx : LinearIndependent ℤ x) (j) : expand A x j ≠ 0 := by
  intro h
  have hi := pivot_independent A x hx
  have hz : ∑ i, A.entry i j • expand A x (A.pivot i) = 0 := by
    funext l
    simp [Finset.sum_apply, ← expand_compatible A x j l, h]
  obtain ⟨i, hne⟩ := A.nonzeroColumn j
  exact hne (Fintype.linearIndependent_iff.mp hi _ hz i)

private theorem span_le : Submodule.span ℤ (Set.range (expand A x)) ≤
    Submodule.span ℤ (Set.range x) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  have h : expand A x j = ∑ a, diagramIntegerEntry A a j • x a := by
    ext l; simp [expand, Finset.sum_apply]
  rw [h]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

theorem rank_iff : Module.finrank ℤ (Submodule.span ℤ (Set.range (expand A x))) = r ↔
    LinearIndependent ℤ x := by
  have hu := Submodule.finrank_mono (span_le A x)
  have hc := finrank_range_le_card (R := ℤ) x
  simp only [Fintype.card_fin] at hc
  change Module.finrank ℤ (Submodule.span ℤ (Set.range x)) ≤ r at hc
  constructor
  · intro h
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    simp only [Fintype.card_fin, Set.finrank]
    omega
  · intro hx
    have hp := finrank_span_eq_card (pivot_independent A x hx)
    have hl := Submodule.finrank_mono (Submodule.span_mono (R := ℤ)
      (show Set.range (fun i ↦ expand A x (A.pivot i)) ⊆ Set.range (expand A x) from
        fun _ ⟨i,hi⟩ ↦ ⟨_,hi⟩))
    simp only [Fintype.card_fin] at hp
    omega

end SigabaNeo.Rogers.AllOrders

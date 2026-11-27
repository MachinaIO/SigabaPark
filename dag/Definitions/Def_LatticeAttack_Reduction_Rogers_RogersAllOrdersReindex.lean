import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersAllOrdersRank
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersAllOrdersNormal
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersAllOrdersEvaluation

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers
namespace AllOrders
open PlaneParam

abbrev Index (n k : ℕ) (r : Fin k) := Σ q, Σ _ : Diagram (r.val+1) k (q+1), Frame.independent n (r.val+1)
abbrev Fiber (n k : ℕ) (r : Fin k) := (tupleRankIndex (k := k) (n := n) (Nat.zero_lt_of_lt r.isLt)) ⁻¹' {r}

def tuple {n k} {r : Fin k} (t : Index n k r) : IntegerTuple n k := fun j ↦
  ⟨expand t.2.1 (fun i ↦ (t.2.2.val i).val) j, expand_ne_zero _ _ t.2.2.property j⟩

def toFiber {n k} {r : Fin k} (t : Index n k r) : Fiber n k r := by
  refine ⟨tuple t, ?_⟩
  change tupleRankIndex _ _ = r
  apply Fin.ext
  have hr : tupleRank (tuple t) = r.val+1 := (rank_iff t.2.1 (fun i ↦ (t.2.2.val i).val)).mpr t.2.2.property
  simp [tupleRankIndex,hr]

def UniquePivots (n k : ℕ) (r : Fin k) := ∀ {q s} {A : Diagram (r.val+1) k (q+1)}
    {B : Diagram (r.val+1) k (s+1)} {z : Fin k → Fin n → ℤ}, Compatible A z →
    Compatible B z → LinearIndependent ℤ (fun i ↦ z (A.pivot i)) →
    LinearIndependent ℤ (fun i ↦ z (B.pivot i)) → A.pivot = B.pivot

private theorem pivot_step {n k m q s} {A : Diagram m k (q+1)} {B : Diagram m k (s+1)}
    {z : Fin k → Fin n → ℤ} (hB : Compatible B z)
    (hi : LinearIndependent ℤ (fun i ↦ z (A.pivot i))) (i : Fin m)
    (prev : ∀ a < i, A.pivot a = B.pivot a) : B.pivot i ≤ A.pivot i := by
  classical
  by_contra! h
  let j := A.pivot i
  have he (a : Fin m) :
      B.entry a j • z (B.pivot a) = B.entry a j • z (A.pivot a) := by
    by_cases ha : a < i
    · rw [prev a ha]
    · simp [B.echelon a j (h.trans_le (B.increasing.monotone (le_of_not_gt ha)))]
  have hz : ∑ a, B.entry a j • z (A.pivot a) = ((s+1 : ℕ) : ℤ) • z j := by
    simp_rw [← he]
    funext l
    simpa [Finset.sum_apply] using (hB j l).symm
  let d (a : Fin m) : ℤ := (if a = i then ((s+1 : ℕ) : ℤ) else 0) - B.entry a j
  have hd : ∑ a, d a • z (A.pivot a) = 0 := by
    simp only [d, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, hz, j, sub_self]
  have := Fintype.linearIndependent_iff.mp hi d hd i
  simp [d, B.echelon i j h] at this
  omega

theorem uniquePivots (n k : ℕ) (r : Fin k) : UniquePivots n k r := by
  intro q s A B z hA hB hi hj
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    exact le_antisymm (pivot_step hA hj i fun a ha ↦ (ih a ha).symm) (pivot_step hB hi i ih)

def HasDiagram (n k : ℕ) (r : Fin k) := ∀ z : IntegerTuple n k, tupleRank z = r.val+1 →
    ∃ q, ∃ A : Diagram (r.val+1) k (q+1), Compatible A (fun j ↦ (z j).val)

theorem injective {n k} {r : Fin k} : Function.Injective (@toFiber n k r) := by
  have hu := @uniquePivots n k r
  rintro ⟨q,A,x⟩ ⟨s,B,y⟩ h
  have he := congrArg (fun t : Fiber n k r ↦ fun j ↦ (t.val j).val) h
  change expand A (fun i ↦ (x.val i).val) = expand B (fun i ↦ (y.val i).val) at he
  have hp := hu (expand_compatible A _) (he.symm ▸ expand_compatible B _)
    (pivot_independent A _ x.property) (he.symm ▸ pivot_independent B _ y.property)
  have hd := diagram_unique_of_pivots (expand_compatible A _) (he.symm ▸ expand_compatible B _)
    (pivot_independent A _ x.property) hp
  obtain ⟨rfl,hAB⟩ := Sigma.mk.inj hd
  cases eq_of_heq hAB
  have hv := expand_injective A he
  have hxy : x = y := Subtype.ext (funext fun i ↦ Subtype.ext (congrFun hv i))
  cases hxy
  rfl

theorem surjective {n k} {r : Fin k} : HasDiagram n k r → Function.Surjective (@toFiber n k r) := by
  intro exists_diagram t
  have h1 := tupleRankIndex_succ (Nat.zero_lt_of_lt r.isLt : 0 < k) t.val
  rw [show tupleRankIndex _ t.val = r from t.property] at h1
  have hr : tupleRank t.val = r.val+1 := h1.symm
  obtain ⟨q,A,hA⟩ := exists_diagram t.val hr
  obtain ⟨x,hx⟩ := (expand_range A _).mpr hA
  have hi : LinearIndependent ℤ x := (rank_iff A x).mp (by rw [hx]; exact hr)
  let y : Frame.independent n (r.val+1) := ⟨fun i ↦ ⟨x i, hi.ne_zero i⟩, hi⟩
  exact ⟨⟨q,A,y⟩, Subtype.ext (funext fun j ↦ Subtype.ext (congrFun hx j))⟩

end AllOrders

theorem rank_reindex_of_normalForm {n k} (r : Fin k) (D : Set (SL n))
    (F : (Fin k → E n) → ℝ≥0∞)
    (he : AllOrders.HasDiagram n k r) :
    rankOrbitSum (Nat.zero_lt_of_lt r.isLt) D F r = basisOrbitSum D F r := by
  let e := Equiv.ofBijective _ ⟨AllOrders.injective, AllOrders.surjective he⟩
  let T (z : IntegerTuple n k) := ∫⁻ g in D,
    F (fun i ↦ WithLp.toLp 2 (g • fun j ↦ ((z i).val j : ℝ))) ∂groupHaar n
  change (∑' z : AllOrders.Fiber n k r, T z.val) = _
  rw [← e.tsum_eq (fun z ↦ T z.val)]
  refine (tsum_sigma (f := fun q t ↦ T (AllOrders.tuple (r := r) ⟨q,t⟩))).trans ?_
  apply tsum_congr
  intro q
  refine (tsum_sigma (f := fun A z ↦ T (AllOrders.tuple (r := r) ⟨q,A,z⟩))).trans ?_
  apply tsum_congr
  intro A
  apply tsum_congr
  intro x
  apply lintegral_congr
  intro g
  apply congrArg F
  funext j
  unfold basisTuple
  rw [diagramTuple_basisChange]
  apply WithLp.ofLp_injective 2
  simp only [WithLp.ofLp_sum]
  change g.val.mulVec (fun l ↦ (PlaneParam.expand A (fun i ↦ (x.val i).val) j l : ℝ)) =
    ∑ a, (diagramIntegerEntry A a j : ℝ) • g.val.mulVec (fun l ↦ ((x.val a).val l : ℝ))
  simp_rw [← Matrix.mulVec_smul]
  rw [← Matrix.mulVec_sum]
  congr 1
  funext l
  simp [PlaneParam.expand, Finset.sum_apply]

end SigabaNeo.Rogers

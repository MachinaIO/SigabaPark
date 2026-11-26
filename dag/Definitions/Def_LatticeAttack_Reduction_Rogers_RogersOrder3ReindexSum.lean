import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder3ReindexNormal
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder3ReindexRank
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder3ReindexUnique

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers
namespace PlaneParam

abbrev Index (n : ℕ) := Σ q, Σ _ : Diagram 2 3 (q+1), orderTwoIndependent n
abbrev Fiber (n : ℕ) := (tupleRankIndex (k := 3) (n := n) (by decide)) ⁻¹' {(1 : Fin 3)}

def tuple {n} (t : Index n) : IntegerTuple n 3 := fun j ↦
  ⟨expand t.2.1 (fun i ↦ (t.2.2.val i).val) j, expand_ne_zero _ _ t.2.2.property j⟩

def toFiber {n} (t : Index n) : Fiber n := by
  refine ⟨tuple t, ?_⟩
  change tupleRankIndex _ _ = 1
  apply Fin.ext
  have hr : tupleRank (tuple t) = 2 := (rank_iff t.2.1 (fun i ↦ (t.2.2.val i).val)).mpr t.2.2.property
  simp [tupleRankIndex,hr]

theorem injective {n} : Function.Injective (@toFiber n) := by
  rintro ⟨q,A,x⟩ ⟨s,B,y⟩ h
  have he := congrArg (fun t : Fiber n ↦ fun j ↦ (t.val j).val) h
  change expand A (fun i ↦ (x.val i).val) = expand B (fun i ↦ (y.val i).val) at he
  have hd := diagram_unique (expand_compatible A _) (he.symm ▸ expand_compatible B _)
    (pivot_independent A _ x.property) (he.symm ▸ pivot_independent B _ y.property)
  obtain ⟨rfl,hAB⟩ := Sigma.mk.inj hd
  cases eq_of_heq hAB
  have hv := expand_injective A he
  have hxy : x = y := Subtype.ext (funext fun i ↦ Subtype.ext (congrFun hv i))
  cases hxy
  rfl

theorem surjective {n} : Function.Surjective (@toFiber n) := by
  intro t
  have h1 := tupleRankIndex_succ (by decide : 0 < 3) t.val
  rw [show tupleRankIndex _ t.val = 1 from t.property] at h1
  have hr : tupleRank t.val = 2 := h1.symm
  obtain ⟨q,A,hA⟩ := exists_diagram t.val hr
  obtain ⟨x,hx⟩ := (expand_range A _).mpr hA
  have hi : LinearIndependent ℤ x := (rank_iff A x).mp (by rw [hx]; exact hr)
  let y : orderTwoIndependent n := ⟨fun i ↦ ⟨x i, hi.ne_zero i⟩, hi⟩
  exact ⟨⟨q,A,y⟩, Subtype.ext (funext fun j ↦ Subtype.ext (congrFun hx j))⟩

end PlaneParam

theorem rankTwo_reindex (n : ℕ) (D : Set (SL n)) (F : (Fin 3 → E n) → ℝ≥0∞) :
    rankOrbitSum (by decide) D F 1 = planeOrbitSum D F := by
  let e := Equiv.ofBijective _ (And.intro (@PlaneParam.injective n) PlaneParam.surjective)
  let T (z : IntegerTuple n 3) := ∫⁻ g in D,
    F (fun i ↦ WithLp.toLp 2 (g • fun j ↦ ((z i).val j : ℝ))) ∂groupHaar n
  change (∑' z : PlaneParam.Fiber n, T z.val) = _
  rw [← e.tsum_eq (fun z ↦ T z.val)]
  refine (tsum_sigma (f := fun q t ↦ T (PlaneParam.tuple ⟨q,t⟩))).trans ?_
  apply tsum_congr
  intro q
  refine (tsum_sigma (f := fun A z ↦ T (PlaneParam.tuple ⟨q,A,z⟩))).trans ?_
  apply tsum_congr
  intro A
  apply tsum_congr
  intro x
  apply lintegral_congr
  intro g
  apply congrArg F
  funext j
  unfold planeTuple
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

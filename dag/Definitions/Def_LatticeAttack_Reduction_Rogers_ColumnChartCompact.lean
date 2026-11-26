import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnHaarCoordinates
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit true

open Set
namespace SigabaNeo.Rogers

private abbrev M (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
private abbrev Logs (d : ℕ) := (Fin (d+1) → ℝ) × (UpperEntry (d+1) → ℝ)

private def coords (d : ℕ) : Logs d →ₗ[ℝ] ColumnParameters d × ℝ where
  toFun z := (((fun i ↦ z.1 i.succ - z.1 i.castSucc), z.2), ∑ i, z.1 i)
  map_add' x y := by ext <;> simp [Finset.sum_add_distrib]; ring
  map_smul' r x := by ext <;> simp [Finset.mul_sum, mul_sub]

private theorem compactCoords {d : ℕ} (K : Set (ColumnParameters d)) (hK : IsCompact K) :
    IsCompact (coords d ⁻¹' (K ×ˢ {0})) := by
  apply LinearMap.isClosedEmbedding_of_injective (f := coords d) _ |>.isCompact_preimage
  · exact hK.prod isCompact_singleton
  · apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨x,v⟩ he
    have hs : ∑ i, x i = 0 := congrArg Prod.snd he
    have hv : v = 0 := congrArg (fun z ↦ z.1.2) he
    have hc (i : Fin (d+1)) : x i = x 0 := by
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
        have h : x i.succ - x i.castSucc = 0 := congrArg (fun z ↦ z.1.1 i) he
        exact (sub_eq_zero.mp h).trans ih
    simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have h0 : x 0 = 0 := (mul_eq_zero.mp hs).resolve_left (by positivity)
    exact Prod.ext (funext fun i ↦ (hc i).trans h0) hv

private theorem compactO (n : ℕ) : IsCompact {k : M n | k.transpose * k = 1} := by
  let B : Set (M n) := univ.pi fun _ ↦ univ.pi fun _ ↦ Icc (-1 : ℝ) 1
  have hb : IsCompact B := isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc
  apply hb.of_isClosed_subset (isClosed_eq (by fun_prop) continuous_const)
  intro k hk i _ j _
  have h := congrArg (fun m : M n ↦ m j j) hk
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  have hs := Finset.single_le_sum (f := fun t ↦ k t j * k t j)
    (fun t _ ↦ mul_self_nonneg _) (Finset.mem_univ i)
  exact ⟨by nlinarith, by nlinarith⟩

private def upper {n : ℕ} (v : UpperEntry n → ℝ) : M n :=
  fun i j ↦ if h : i < j then v ⟨(i,j), h⟩ else if i = j then 1 else 0

theorem columnChartCompactPreimage (d : ℕ) (_ : 1 ≤ d) (f : SL (d+1) → ColumnParameters d)
    (hf : IsColumnChart f) (K : Set (ColumnParameters d)) (hK : IsCompact K) :
    IsCompact (f ⁻¹' K) := by
  classical
  let F (q : M (d+1) × Logs d) :=
    q.1 * Matrix.diagonal (fun i ↦ Real.exp (q.2.1 i)) * upper q.2.2
  have hF : Continuous F := by
    apply Continuous.mul
    · apply continuous_fst.mul
      apply Continuous.matrix_diagonal
      fun_prop
    · apply continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
      dsimp [upper]
      split <;> fun_prop
  let S := {k : M (d+1) | k.transpose * k = 1} ×ˢ (coords d ⁻¹' (K ×ˢ {0}))
  have hS : IsCompact S := (compactO _).prod (compactCoords K hK)
  suffices heq : f ⁻¹' K = (fun g : SL (d+1) ↦ g.val) ⁻¹' (F '' S) by
    rw [heq]
    exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage (hS.image hF)
  ext g
  constructor
  · intro hg
    change f g ∈ K at hg
    obtain ⟨k,u,a,hk,ha,hu,hz,hg',ht,hv⟩ := (hf.2 g _).mpr rfl
    have hU : u.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular (M := u) (fun {_ _} h ↦ hz _ _ h)]
      simp [hu]
    have hkdet := congrArg Matrix.det hk
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hkdet
    have hdet := congrArg Matrix.det hg'
    simp only [g.property, Matrix.det_mul, Matrix.det_diagonal, hU, mul_one] at hdet
    have hp := Finset.prod_pos (s := Finset.univ) (fun i _ ↦ ha i)
    have hkpos : 0 < k.det := by by_contra! h; nlinarith [mul_nonpos_of_nonpos_of_nonneg h hp.le]
    have hk1 : k.det = 1 := by nlinarith
    have hprod : ∏ i, a i = 1 := by simpa [hk1] using hdet.symm
    refine ⟨(k, (fun i ↦ Real.log (a i), (f g).2)), ⟨hk, ?_, ?_⟩, ?_⟩
    · change ((_, _) : ColumnParameters d) ∈ K
      simpa only [ht, Prod.mk.eta] using hg
    · change ∑ i, Real.log (a i) = 0
      rw [← Real.log_prod (fun i _ ↦ (ha i).ne'), hprod, Real.log_one]
    · have hupper : upper (f g).2 = u := by
        rw [← hv]
        ext i j
        rcases lt_trichotomy i j with h | rfl | h
        · simp [upper,h]
        · simp [upper,hu]
        · simp [upper,h.not_gt,h.ne',hz i j h]
      simpa [F, Real.exp_log (ha _), hupper] using hg'.symm
  · rintro ⟨⟨k,x,v⟩, ⟨hk,hp,_⟩,hg⟩
    let p := ((coords d (x,v)).1)
    have he : f g = p := (hf.2 g p).mp
      ⟨k,upper v,fun i ↦ Real.exp (x i),hk,fun _ ↦ Real.exp_pos _,by simp [upper],
        fun i j h ↦ by simp [upper,h.not_gt,h.ne'],hg.symm,by simp [p,coords],
        funext fun i ↦ dite_eq_left i.property⟩
    change f g ∈ K
    rw [he]
    exact hp

#print axioms columnChartCompactPreimage
end SigabaNeo.Rogers

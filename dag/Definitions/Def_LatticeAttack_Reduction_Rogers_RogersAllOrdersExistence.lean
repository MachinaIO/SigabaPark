import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersAllOrdersReindex
import Mathlib.Data.Fin.Tuple.Sort

set_option autoImplicit true

noncomputable section
open Matrix Finset
namespace SigabaNeo.Rogers.AllOrders
open PlaneParam

private theorem exists_minor {r k} (v : Fin k → Fin r → ℤ)
    (c : Fin r → Fin k → ℤ) (hc : ∀ i, ∑ j, c i j • v j = (1 : Matrix (Fin r) (Fin r) ℤ) i) :
    ∃ p : Fin r → Fin k, (Matrix.of fun i ↦ v (p i)).det ≠ 0 := by
  classical
  by_contra! h
  let f := (Matrix.detRowAlternating : (Fin r → ℤ) [⋀^Fin r]→ₗ[ℤ] ℤ).toMultilinearMap
  have he := f.map_sum (fun i j ↦ c i j • v j)
  simp_rw [hc, f.map_smul_univ] at he
  have hz (p : Fin r → Fin k) : f (fun i ↦ v (p i)) = 0 := h p
  simp only [hz, smul_zero, sum_const_zero] at he
  exact one_ne_zero (Matrix.det_one.symm.trans he)

private theorem minimal_rows {r k} (v : Fin k → Fin r → ℤ)
    (hv : ∃ p : Fin r → Fin k, (Matrix.of fun i ↦ v (p i)).det ≠ 0) :
    ∃ p : Fin r → Fin k, StrictMono p ∧ (Matrix.of fun i ↦ v (p i)).det ≠ 0 ∧
      ∀ i j, j < p i → ((Matrix.of fun a ↦ v (p a)).updateRow i (v j)).det = 0 := by
  classical
  let good (p : Fin r → Fin k) := (Matrix.of fun a ↦ v (p a)).det ≠ 0
  let weight (p : Fin r → Fin k) := ∑ a, (p a).val
  obtain ⟨u,hu,hmin⟩ := (univ.filter good).exists_min_image weight
    (by obtain ⟨p,hp⟩ := hv; exact ⟨p,mem_filter.mpr ⟨mem_univ _,hp⟩⟩)
  let σ := Tuple.sort u
  let p := u ∘ σ
  have hU := (mem_filter.mp hu).2
  have hP : good p := by
    change ((Matrix.of fun a ↦ v (u a)).submatrix σ id).det ≠ 0
    rw [Matrix.det_permute]
    exact mul_ne_zero (Units.ne_zero _) hU
  have inj : Function.Injective p := by
    intro i j hij
    exact (Matrix.linearIndependent_rows_of_det_ne_zero hP).injective (congrArg v hij)
  refine ⟨p, (Tuple.monotone_sort u).strictMono_of_injective inj, hP, ?_⟩
  intro i j hj
  by_contra h
  let p' := Function.update p i j
  have hp' : good p' := by
    have eq : (Matrix.of fun a ↦ v (p' a)) = (Matrix.of fun a ↦ v (p a)).updateRow i (v j) := by
      ext a b
      by_cases ha : a = i <;> simp [p', Function.update, ha, Matrix.updateRow_apply]
    change (Matrix.of fun a ↦ v (p' a)).det ≠ 0
    rwa [eq]
  have H := hmin p' (mem_filter.mpr ⟨mem_univ _,hp'⟩)
  have hw : weight p = weight u := Equiv.sum_comp σ (fun a ↦ (u a).val)
  rw [← hw] at H
  unfold weight at H
  rw [← sum_erase_add _ _ (mem_univ i), ← sum_erase_add _ (fun a ↦ (p' a).val) (mem_univ i)] at H
  have eq : ∑ a ∈ univ.erase i, (p' a).val = ∑ a ∈ univ.erase i, (p a).val :=
    sum_congr rfl fun a ha ↦ by simp [p', (mem_erase.mp ha).1]
  simp only [eq,p',Function.update_self] at H
  omega

theorem hasDiagram_succ {n k r : ℕ} (z : IntegerTuple n (k+1)) (hr : tupleRank z = r+1) :
    ∃ q, ∃ A : Diagram (r+1) (k+1) (q+1), Compatible A (fun j ↦ (z j).val) := by
  classical
  let S := Submodule.span ℤ (Set.range fun j ↦ (z j).val)
  let b := Module.finBasisOfFinrankEq ℤ S hr
  let u (j) : S := ⟨(z j).val, Submodule.subset_span (Set.mem_range_self j)⟩
  let v (j : Fin (k+1)) (i : Fin (r+1)) := b.repr (u j) i
  have hsp : Submodule.span ℤ (Set.range u) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff S _).mpr rfl
  have hc (i) := (Submodule.mem_span_range_iff_exists_fun ℤ).mp
    (show b i ∈ Submodule.span ℤ (Set.range u) from hsp ▸ Submodule.mem_top)
  choose c hc using hc
  have hcoord (i) : ∑ j, c i j • v j = (1 : Matrix (Fin (r+1)) _ ℤ) i := by
    funext a
    have H := congrArg (fun x : S ↦ b.repr x a) (hc i)
    simpa [v, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply, eq_comm] using H
  obtain ⟨p,hp,hd,he⟩ := minimal_rows v (exists_minor v c hcoord)
  let M := Matrix.of fun i ↦ v (p i)
  let e (i j) := M.det.sign * (Mᵀ.cramer (v j)) i
  have hs : M.det.sign * M.det = (M.det.natAbs : ℤ) := Int.sign_mul_self _
  have rel (j l) : (M.det.natAbs : ℤ) * (z j).val l = ∑ i, e i j * (z (p i)).val l := by
    have hw (j l) : (z j).val l = ∑ a, v j a * (b a).val l := by
      have H := congrArg (fun x : S ↦ x.val l) (b.sum_repr (u j))
      simpa [-Module.Basis.sum_repr, v, u, Finset.sum_apply] using H.symm
    have H := Mᵀ.mulVec_cramer (v j)
    rw [← hs, hw]
    simp_rw [hw (p _), e, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    have h := congrFun H a
    change ∑ i, M i a * Mᵀ.cramer (v j) i = Mᵀ.det * v j a at h
    rw [det_transpose] at h
    calc
      _ = M.det.sign * (M.det * v j a) * (b a).val l := by ring
      _ = _ := by rw [← h, Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; dsimp [M]; ring
  have ech (i j) (h : j < p i) : e i j = 0 := by
    have H := he i j h
    change (M.updateRow i (v j)).det = 0 at H
    apply mul_eq_zero_of_right
    change (Mᵀ.updateCol i (v j)).det = 0
    rw [← Matrix.det_transpose, Matrix.updateCol_transpose, Matrix.transpose_transpose, H]
  have h0 : p 0 = 0 := by
    by_contra h
    have hi (i) := (Fin.pos_iff_ne_zero.mpr h).trans_le (hp.monotone (Fin.zero_le i))
    apply (z 0).property
    funext l
    have H := rel 0 l
    simp only [fun i ↦ ech i 0 (hi i), zero_mul, sum_const_zero] at H
    exact (mul_eq_zero.mp H).resolve_left (by exact_mod_cast Int.natAbs_ne_zero.mpr hd)
  obtain ⟨q,A,_,hA⟩ := exists_reduced (fun j ↦ (z j).property) hp h0
    ⟨M.det.natAbs, ⟨⟨Int.natAbs_pos.mpr hd, e, by
      intro i a
      change M.det.sign * Mᵀ.cramer (M a) i = _
      rw [Matrix.cramer_transpose_row_self]
      by_cases h : i = a <;> simp [h,hs], ech, rel⟩⟩⟩
  exact ⟨q,A,hA⟩

end SigabaNeo.Rogers.AllOrders

import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder3Reindex

set_option autoImplicit true

noncomputable section
namespace SigabaNeo.Rogers.PlaneParam

/-- A Cramer presentation before division by its content. -/
structure Presentation {n} (z : Fin 3 → Fin n → ℤ) (p : Fin 2 → Fin 3) (d : ℕ) where
  pos : 0 < d
  entry : Fin 2 → Fin 3 → ℤ
  pivot : ∀ i a, entry i (p a) = if i = a then (d : ℤ) else 0
  echelon : ∀ i j, j < p i → entry i j = 0
  relation : ∀ j l, (d : ℤ) * z j l = ∑ i, entry i j * z (p i) l

theorem exists_reduced {n} {z : Fin 3 → Fin n → ℤ} (hnz : ∀ j, z j ≠ 0)
    {p : Fin 2 → Fin 3} (hp : StrictMono p) (h0 : p 0 = 0)
    (h : ∃ d, Nonempty (Presentation z p d)) :
    ∃ q, ∃ A : Diagram 2 3 (q+1), A.pivot = p ∧ Compatible A z := by
  classical
  let d := Nat.find h
  obtain ⟨C⟩ : Nonempty (Presentation z p d) := Nat.find_spec h
  have hd : 0 < d := C.pos
  have prim (e : ℕ) (he : ∀ i j, (e : ℤ) ∣ C.entry i j) : e = 1 := by
    have hed : e ∣ d := by
      have hh := he 0 (p 0)
      rw [C.pivot, ite_eq_left rfl] at hh
      exact_mod_cast hh
    have hep := Nat.pos_of_dvd_of_pos hed hd
    by_contra hne
    obtain ⟨s, hs⟩ := hed
    have hs' : (d : ℤ) = (e : ℤ) * (s : ℤ) := by exact_mod_cast hs
    have hsp : 0 < s := by by_contra! hh; simp [show s = 0 by omega] at hs; omega
    have hlt : s < d := by rw [hs]; simpa using Nat.mul_lt_mul_of_pos_right (show 1 < e by omega) hsp
    have hE : (e : ℤ) ≠ 0 := by exact_mod_cast hep.ne'
    choose b hb using he
    apply Nat.find_min h hlt
    refine ⟨⟨hsp, b, ?_, ?_, ?_⟩⟩
    · intro i a
      apply mul_left_cancel₀ hE
      rw [← hb, C.pivot, mul_ite, hs', mul_zero]
    · intro i j hij
      exact (mul_eq_zero.mp ((hb i j).symm.trans (C.echelon i j hij))).resolve_left hE
    · intro j l
      apply mul_left_cancel₀ hE
      simpa only [Finset.mul_sum, ← mul_assoc, ← hb, ← hs'] using C.relation j l
  obtain ⟨q,hq⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  change d = q + 1 at hq
  let A : Diagram 2 3 (q+1) :=
    { entry := C.entry
      pivot := p
      increasing := hp
      first := by intro i hi; have : i = 0 := Fin.ext hi; simp [this,h0]
      pivotColumn := by simpa only [← hq] using C.pivot
      echelon := C.echelon
      nonzeroColumn := by
        intro j
        by_contra! hz
        apply hnz j
        funext l
        have hh : (d : ℤ) * z j l = 0 := by simpa only [hz, zero_mul, Finset.sum_const_zero] using C.relation j l
        exact (mul_eq_zero.mp hh).resolve_left
          (by exact_mod_cast hd.ne')
      primitive := prim }
  exact ⟨q,A,rfl,by simpa only [Compatible, A, ← hq] using C.relation⟩

private def det2 (u v : Fin 2 → ℤ) := u 0 * v 1 - u 1 * v 0

private theorem cramer {n} {z : Fin 3 → Fin n → ℤ} (v : Fin 3 → Fin 2 → ℤ)
    (w : Fin 2 → Fin n → ℤ) (hw : ∀ j l, z j l = v j 0 * w 0 l + v j 1 * w 1 l)
    (p : Fin 2 → Fin 3) (h : det2 (v (p 0)) (v (p 1)) ≠ 0)
    (he : ∀ j, j < p 1 → det2 (v (p 0)) (v j) = 0) (hp : p 0 = 0) :
    ∃ d, Nonempty (Presentation z p d) := by
  let D := det2 (v (p 0)) (v (p 1))
  let s := Int.sign D
  have hs : s * D = (D.natAbs : ℤ) := Int.sign_mul_self D
  refine ⟨D.natAbs, ⟨⟨Int.natAbs_pos.mpr h,
    fun i j ↦ s * (if i = 0 then det2 (v j) (v (p 1)) else det2 (v (p 0)) (v j)),
    ?_, ?_, ?_⟩⟩⟩
  · intro i a
    fin_cases i <;> fin_cases a <;> simp [s,D,det2, mul_comm, Int.sign_mul_self]
    right; ring
  · intro i j hlt
    fin_cases i
    · simp [hp] at hlt
    · simp [he j hlt]
  · intro j l
    rw [← hs]
    simp [Fin.sum_univ_two, D, det2, hw]
    ring

theorem exists_diagram {n} (z : IntegerTuple n 3) (hr : tupleRank z = 2) :
    ∃ q, ∃ A : Diagram 2 3 (q+1), Compatible A (fun j ↦ (z j).val) := by
  classical
  let S := Submodule.span ℤ (Set.range fun j ↦ (z j).val)
  let b := Module.finBasisOfFinrankEq ℤ S hr
  let u (j) : S := ⟨(z j).val, Submodule.subset_span (Set.mem_range_self j)⟩
  let v (j : Fin 3) (i : Fin 2) := b.repr (u j) i
  have hw (j l) : (z j).val l = v j 0 * (b 0).val l + v j 1 * (b 1).val l := by
    have hh := congrArg (fun x : S ↦ x.val l) (b.sum_repr (u j))
    simpa [-Module.Basis.sum_repr, Fin.sum_univ_two, v, u] using hh.symm
  have hex : ∃ j, det2 (v 0) (v j) ≠ 0 := by
    by_contra! hh
    let f (x : S) := v 0 0 * b.repr x 1 - v 0 1 * b.repr x 0
    have hall (x : S) : f x = 0 := by
      obtain ⟨x,hx⟩ := x
      induction hx using Submodule.span_induction with
      | mem x h => obtain ⟨j,rfl⟩ := h; exact hh j
      | zero => change f 0 = 0; simp [f]
      | add x y hx hy h₁ h₂ =>
        change f (⟨x,hx⟩ + ⟨y,hy⟩) = 0
        simp only [f, map_add, Finsupp.add_apply, mul_add]
        dsimp [f] at h₁ h₂
        linarith
      | smul a x hx h =>
        change f (a • ⟨x,hx⟩) = 0
        simp only [f, map_smul, Finsupp.smul_apply, smul_eq_mul]
        dsimp [f] at h
        linear_combination a * h
    have h₀ : v 0 0 = 0 := by simpa [f, Finsupp.single_apply] using hall (b 1)
    have h₁ : v 0 1 = 0 := by simpa [f, Finsupp.single_apply] using hall (b 0)
    exact (z 0).property (funext fun l ↦ by simpa [h₀,h₁] using hw 0 l)
  let j := Finset.min' (Finset.univ.filter fun j ↦ det2 (v 0) (v j) ≠ 0)
    (by obtain ⟨t,ht⟩ := hex; exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩⟩)
  have hj := Finset.mem_filter.mp (Finset.min'_mem _ _ : j ∈ _)
  have hj0 : j ≠ 0 := fun h ↦ hj.2 (by change det2 (v 0) (v j) = 0; rw [h]; unfold det2; ring)
  let p : Fin 2 → Fin 3 := ![0,j]
  have hp : StrictMono p := Fin.strictMono_iff_lt_succ.mpr (by intro i; fin_cases i; exact Fin.pos_iff_ne_zero.mpr hj0)
  obtain ⟨q,A,_,hA⟩ := exists_reduced (fun i ↦ (z i).property) hp rfl
    (cramer v (fun i ↦ (b i).val) hw p hj.2 (by
      intro t ht
      by_contra hn
      exact (not_le_of_gt ht) (Finset.min'_le _ t (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩))) rfl)
  exact ⟨q,A,hA⟩

end SigabaNeo.Rogers.PlaneParam

import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnHaarCoordinates

set_option autoImplicit true

open Matrix
namespace SigabaNeo.Rogers

theorem columnParams_mul_diagonal {d : ℕ} {g b : SL (d+1)} {p : ColumnParameters d}
    (hp : HasColumnParameters g p) (s : Fin (d+1) → ℝ) (hs : ∀ i, 0 < s i)
    (hb : b.val = diagonal s) : HasColumnParameters (g * b)
      (fun i ↦ p.1 i + (Real.log (s i.succ) - Real.log (s i.castSucc)),
       fun i ↦ p.2 i * s i.val.2 / s i.val.1) := by
  obtain ⟨k,u,a,hk,ha,hu,hz,hg,ht,hv⟩ := hp
  rw [← ht, ← hv]
  let v : Matrix _ _ ℝ := fun i j ↦ u i j * s j / s i
  refine ⟨k,v,fun i ↦ a i * s i,hk,fun i ↦ mul_pos (ha i) (hs i),?_,?_,?_,?_,rfl⟩
  · intro i
    simp [v, hu, (hs i).ne']
  · intro i j h
    simp [v, hz i j h]
  · change g.val * b.val = _
    rw [hg, hb]
    simp only [Matrix.mul_assoc]
    congr 1
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_mul]
    dsimp [v]
    field_simp [(hs i).ne'] <;> ring
  · funext i
    simp [Real.log_mul (ha _).ne' (hs _).ne']
    ring

theorem columnParams_mul_unitriangular {d : ℕ} {g b : SL (d+1)} {p : ColumnParameters d}
    (hp : HasColumnParameters g p) (hb : ∀ i, b.val i i = 1)
    (hz : ∀ i j, j < i → b.val i j = 0) :
    ∃ u : Matrix (Fin (d+1)) (Fin (d+1)) ℝ,
      (∀ i, u i i = 1) ∧ (∀ i j, j < i → u i j = 0) ∧
      (∀ i : UpperEntry (d+1), u i.val.1 i.val.2 = p.2 i) ∧
      HasColumnParameters (g * b) (p.1, fun i ↦ (u * b.val) i.val.1 i.val.2) := by
  obtain ⟨k,u,a,hk,ha,hu,hl,hg,ht,hv⟩ := hp
  rw [← ht, ← hv]
  refine ⟨u,hu,hl,fun _ ↦ rfl,k,u * b.val,a,hk,ha,?_,?_,?_,rfl,rfl⟩
  · intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hu, hb, one_mul]
    · intro j _ h
      rcases lt_or_gt_of_ne h with h | h
      · simp [hl _ _ h]
      · simp [hz _ _ h]
    · simp
  · intro i j h
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl' : l < i
    · simp [hl _ _ hl']
    · simp [hz _ _ (lt_of_lt_of_le h (le_of_not_gt hl'))]
  · change g.val * b.val = _
    rw [hg, Matrix.mul_assoc]

open MeasureTheory in
theorem columnChart_map_rightAction {d : ℕ} {f : SL (d+1) → ColumnParameters d}
    (hf : IsColumnChart f) (b : SL (d+1)) (T : ColumnParameters d → ColumnParameters d)
    (hT : Measurable T) (h : ∀ g, HasColumnParameters (g * b) (T (f g))) :
    ((groupHaar (d+1)).map f).map T = (groupHaar (d+1)).map f := by
  letI : BorelSpace (SL (d+1)) := ⟨rfl⟩
  letI := groupHaar_rightInvariant (d+1)
  have e : T ∘ f = f ∘ (· * b) := funext fun g ↦ ((hf.2 _ _).mp (h g)).symm
  rw [Measure.map_map hT hf.1, e, ← Measure.map_map hf.1 (measurable_mul_const b),
    map_mul_right_eq_self]

#print axioms columnParams_mul_diagonal
#print axioms columnParams_mul_unitriangular
#print axioms columnChart_map_rightAction
end SigabaNeo.Rogers

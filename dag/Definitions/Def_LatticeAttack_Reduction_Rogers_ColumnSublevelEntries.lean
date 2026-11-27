module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRPotential

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Rogers

/-- A uniform bound for the diagonal of a size-reduced triangular factor gives an
integral entry bound after undoing the fixed real basis change. -/
theorem columnEntries_of_diagonalBound {n : ℕ} {x : SL n} (a : ColumnCandidate x)
    (D : ℝ) (hd : ∀ c : ColumnCandidate x, c.potential ≤ a.potential → ∀ i, c.r i i ≤ D) :
    ∃ B : ℤ, ∀ c : ColumnCandidate x, c.potential ≤ a.potential → ∀ i j, |c.γ.val i j| ≤ B := by
  classical
  let M := ∑ i : Fin n, ∑ j : Fin n, |x⁻¹.val i j|
  obtain ⟨B, hB⟩ := exists_int_ge (M * (n * max D 0))
  refine ⟨B, ?_⟩
  intro c hc i j
  have hr (u v : Fin n) : |c.r u v| ≤ max D 0 := by
    rcases lt_trichotomy u v with h | rfl | h
    · exact (c.reduced u v h).trans (by linarith [hd c hc u, le_max_left D 0, c.positive u])
    · rw [abs_of_pos (c.positive u)]
      exact (hd c hc u).trans (le_max_left ..)
    · simp [c.triangular u v h]
  have hk (u v : Fin n) : |c.k u v| ≤ 1 := by
    have h := congrArg (fun m : Matrix (Fin n) (Fin n) ℝ ↦ m v v) c.orthogonal
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    have hs := Finset.single_le_sum (f := fun t ↦ c.k t v * c.k t v)
      (fun t _ ↦ mul_self_nonneg _) (Finset.mem_univ u)
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hkr (u : Fin n) : |(c.k * c.r) u j| ≤ n * max D 0 := by
    rw [Matrix.mul_apply]
    calc
      _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin n, 1 * max D 0 := Finset.sum_le_sum fun t _ ↦ by
        rw [abs_mul]
        exact mul_le_mul (hk ..) (hr ..) (abs_nonneg _) zero_le_one
      _ = _ := by simp
  let g := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) c.γ
  have eq : g.val = x⁻¹.val * (c.k * c.r) := by
    rw [← c.factor]
    change g.val = (x⁻¹ * (x * g)).val
    simp
  have e := congrArg (fun m : Matrix (Fin n) (Fin n) ℝ ↦ m i j) eq
  change (c.γ.val i j : ℝ) = _ at e
  suffices h : |(c.γ.val i j : ℝ)| ≤ (B : ℝ) by exact_mod_cast h
  rw [e, Matrix.mul_apply]
  apply le_trans _ hB
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Fin n, |x⁻¹.val i t| * (n * max D 0) := Finset.sum_le_sum fun t _ ↦ by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hkr _) (abs_nonneg _)
    _ = _ := Finset.sum_mul .. |>.symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (Finset.single_le_sum
      (f := fun u ↦ ∑ t : Fin n, |x⁻¹.val u t|) (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ i)) (by positivity)

end SigabaNeo.Rogers

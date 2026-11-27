import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRPotential

set_option autoImplicit true

namespace SigabaNeo.Rogers

private theorem reduceColumn {n : ℕ} (r : Matrix (Fin n) (Fin n) ℝ)
    (hp : ∀ i, 0 < r i i) (ht : ∀ i j, j < i → r i j = 0) (j : Fin n) :
    ∃ u : Fin n → ℤ, u j = 1 ∧ (∀ t, j < t → u t = 0) ∧
      ∀ i, i < j → |∑ t, r i t * (u t : ℝ)| ≤ r i i / 2 := by
  classical
  let v (u : Fin n → ℤ) (i : Fin n) := ∑ t, r i t * (u t : ℝ)
  suffices h : ∀ k : ℕ, k ≤ j.val → ∃ u : Fin n → ℤ, u j = 1 ∧
      (∀ t, j < t → u t = 0) ∧ ∀ i, k ≤ i.val → i < j → |v u i| ≤ r i i / 2 by
    obtain ⟨u, hu, hz, hb⟩ := h 0 (Nat.zero_le _)
    exact ⟨u, hu, hz, fun i ↦ hb i (Nat.zero_le _)⟩
  intro k hk
  generalize hd : j.val - k = d
  induction d using Nat.strong_induction_on generalizing k with
  | ind d ih =>
    by_cases he : k = j.val
    · exact ⟨fun t ↦ if t = j then 1 else 0, by simp, fun t h ↦ by simp [h.ne'],
        fun i h h' ↦ False.elim (by omega)⟩
    · obtain ⟨u, hu, hz, hb⟩ := ih (j.val - (k + 1)) (by omega) (k + 1) (by omega) rfl
      let a : Fin n := ⟨k, by omega⟩
      let z := -round (v u a / r a a)
      let w (t : Fin n) := u t + if t = a then z else 0
      have hv (i : Fin n) : v w i = v u i + r i a * z := by
        simp only [v, w, Int.cast_add, mul_add, Finset.sum_add_distrib]
        simp [apply_ite]
      have haj : a < j := by change k < j.val; omega
      refine ⟨w, by simp [w, haj.ne', hu], fun t h ↦ by simp [w, (haj.trans h).ne', hz t h], ?_⟩
      intro i h hij
      rw [hv]
      by_cases e : i = a
      · subst i
        have eq : v u a + r a a * (z : ℝ) =
            (v u a / r a a - round (v u a / r a a)) * r a a := by
          dsimp [z]
          push_cast
          field_simp [(hp a).ne']
          ring
        rw [eq, abs_mul, abs_of_pos (hp a)]
        nlinarith [mul_le_mul_of_nonneg_right (abs_sub_round (v u a / r a a)) (hp a).le]
      · have hlt : a < i := lt_of_le_of_ne (show a ≤ i from h) (Ne.symm e)
        rw [ht i a hlt, zero_mul, add_zero]
        exact hb i (show k + 1 ≤ i.val from hlt) hij

theorem columnIntegralSizeReduction (n : ℕ) (x : SL n)
    (γ : Matrix.SpecialLinearGroup (Fin n) ℤ) (k r : Matrix (Fin n) (Fin n) ℝ)
    (hk : k.transpose * k = 1)
    (hf : (x * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ).val = k * r)
    (hp : ∀ t, 0 < r t t) (ht : ∀ a b, b < a → r a b = 0) :
    ∃ b : ColumnCandidate x, ∀ t, b.r t t = r t t := by
  classical
  choose u hd hz hb using reduceColumn r hp ht
  let U : Matrix (Fin n) (Fin n) ℤ := fun i j ↦ u j i
  have hu : U.IsUpperTriangular := fun i j h ↦ hz j i h
  let δ : Matrix.SpecialLinearGroup (Fin n) ℤ :=
    ⟨U, by rw [Matrix.det_of_isUpperTriangular hu]; simp [U, hd]⟩
  let φ := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin n)
  let R := r * (φ δ).val
  have entry (i j : Fin n) : R i j = ∑ t, r i t * (u j t : ℝ) := rfl
  have diag (i : Fin n) : R i i = r i i := by
    rw [entry, Finset.sum_eq_single i]
    · simp [hd]
    · intro t _ h
      rcases lt_or_gt_of_ne h with hlt | hgt
      · simp [ht i t hlt]
      · simp [hz i t hgt]
    · simp
  refine ⟨⟨γ * δ, k, R, hk, ?_, fun i ↦ (diag i).symm ▸ hp i, ?_, ?_⟩, diag⟩
  · change (x * φ (γ * δ)).val = k * R
    rw [map_mul, ← mul_assoc, Matrix.SpecialLinearGroup.coe_mul, hf, Matrix.mul_assoc]
  · intro i j h
    rw [entry]
    apply Finset.sum_eq_zero
    intro t _
    by_cases hlt : t < i
    · simp [ht i t hlt]
    · simp [hz j t (lt_of_lt_of_le h (le_of_not_gt hlt))]
  · intro i j h
    rw [diag, entry]
    exact hb j i h

#print axioms columnIntegralSizeReduction
end SigabaNeo.Rogers

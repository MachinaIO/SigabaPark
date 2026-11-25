import Mathlib

open Matrix

theorem solution {K : Type*} [Field K] [DecidableEq K] {m n : ℕ}
    (N : Matrix (Fin m) (Fin n) K) (T : Finset K) (α : Fin m → K) :
    ((Finset.univ : Finset (Fin n → T)).filter
        (fun r => N *ᵥ (fun i => (r i : K)) = α)).card ≤ T.card ^ (n - N.rank) := by
  classical
  -- a maximal linearly independent family of columns
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K N.col
  have : Finite κ := Finite.of_injective a ha
  let _ : Fintype κ := Fintype.ofFinite κ
  have hrank : N.rank = Fintype.card κ := by
    rw [rank_eq_finrank_span_cols, ← hspan, finrank_span_eq_card hli]
  -- the coordinates outside the family
  let S : Set (Fin n) := Set.range a
  have hcardS : Fintype.card S = Fintype.card κ := by
    rw [Set.card_range_of_injective ha]
  -- restricting a solution to the coordinates outside `S` is injective
  let φ : (Fin n → T) → ({j // j ∉ S} → T) := fun r j => r j.1
  have hinj : Set.InjOn φ ((Finset.univ.filter
      (fun r : Fin n → T => N *ᵥ (fun i => (r i : K)) = α)) : Set (Fin n → T)) := by
    intro r hr r' hr' hφ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hr hr'
    -- `d = r − r'` is supported on `S` and in the kernel of `N`
    set d : Fin n → K := fun i => (r i : K) - (r' i : K) with hd
    have hker : N *ᵥ d = 0 := by
      have : N *ᵥ d = N *ᵥ (fun i => (r i : K)) - N *ᵥ (fun i => (r' i : K)) := by
        rw [hd, ← Matrix.mulVec_sub]; rfl
      rw [this, hr, hr', sub_self]
    have hsupp : ∀ j, j ∉ S → d j = 0 := by
      intro j hj
      have := congrFun hφ ⟨j, hj⟩
      simp only [φ] at this
      simp [hd, this]
    -- the kernel equation is a vanishing combination of the independent columns
    have hcomb : ∑ k : κ, d (a k) • N.col (a k) = 0 := by
      have h1 : N *ᵥ d = ∑ j, d j • N.col j := by
        ext i
        simp [Matrix.mulVec, dotProduct, Matrix.col, Finset.sum_apply, mul_comm]
      have h2 : ∑ j, d j • N.col j = ∑ k : κ, d (a k) • N.col (a k) := by
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image a))]
        · rw [Finset.sum_image (fun x _ y _ h => ha h)]
        · intro j _ hj
          have : j ∉ S := by
            rintro ⟨k, rfl⟩; exact hj (Finset.mem_image_of_mem a (Finset.mem_univ k))
          rw [hsupp j this, zero_smul]
      rw [← h2, ← h1, hker]
    have hzero : ∀ k, d (a k) = 0 := by
      have := linearIndependent_iff'.mp hli Finset.univ (fun k => d (a k))
      intro k
      exact this (by simpa [Function.comp_def] using hcomb) k (Finset.mem_univ k)
    funext i
    apply Subtype.ext
    by_cases hi : i ∈ S
    · obtain ⟨k, rfl⟩ := hi
      have := hzero k
      simp only [hd] at this
      exact sub_eq_zero.mp this
    · exact sub_eq_zero.mp (hsupp i hi)
  calc ((Finset.univ : Finset (Fin n → T)).filter
          (fun r => N *ᵥ (fun i => (r i : K)) = α)).card
      ≤ (Finset.univ : Finset ({j // j ∉ S} → T)).card :=
        Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
    _ = T.card ^ (n - N.rank) := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, hrank, ← hcardS,
          Fintype.card_subtype_compl, Fintype.card_fin]

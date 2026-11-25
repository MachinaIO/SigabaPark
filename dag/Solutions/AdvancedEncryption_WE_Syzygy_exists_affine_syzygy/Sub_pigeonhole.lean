import Mathlib

theorem solution {M d : ℕ} (B : ℕ) (v : Fin M → Fin d → ℤ)
    (hv : ∀ j i, |v j i| ≤ B)
    (hM : (2 * M * B + 1) ^ d * (M + 1) < 2 ^ M) :
    ∃ α : Fin M → ℤ, α ≠ 0 ∧ (∀ j, |α j| ≤ 1) ∧ ∑ j, α j = 0 ∧ ∑ j, α j • v j = 0 := by
  classical
  let f : Finset (Fin M) → (Fin d → ℤ) × ℕ := fun S => (fun i => ∑ j ∈ S, v j i, S.card)
  let T : Finset ((Fin d → ℤ) × ℕ) :=
    (Fintype.piFinset fun _ : Fin d => Finset.Icc (-((M : ℤ) * B)) ((M : ℤ) * B)) ×ˢ
      Finset.range (M + 1)
  have hT : T.card = (2 * M * B + 1) ^ d * (M + 1) := by
    simp only [T, Finset.card_product, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Finset.card_range]
    congr 2
    have : (M : ℤ) * B + 1 - -((M : ℤ) * B) = ((2 * M * B + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  have hmaps : ∀ S ∈ (Finset.univ : Finset (Finset (Fin M))), f S ∈ T := by
    intro S _
    simp only [f, T, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_range]
    refine ⟨fun i => ?_, Nat.lt_succ_of_le (by simpa using S.card_le_univ)⟩
    have h1 : |∑ j ∈ S, v j i| ≤ ∑ j ∈ S, (B : ℤ) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hv j i)
    have h2 : ∑ j ∈ S, (B : ℤ) ≤ (M : ℤ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have : (S.card : ℤ) ≤ M := by exact_mod_cast (by simpa using S.card_le_univ)
      exact mul_le_mul_of_nonneg_right this (by positivity)
    exact abs_le.mp (h1.trans h2)
  have hcard : T.card < (Finset.univ : Finset (Finset (Fin M))).card := by
    rw [hT, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]; exact hM
  obtain ⟨S, -, S', -, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  simp only [f, Prod.mk.injEq] at heq
  obtain ⟨hsum, hc⟩ := heq
  let α : Fin M → ℤ := fun j => (if j ∈ S then 1 else 0) - (if j ∈ S' then 1 else 0)
  refine ⟨α, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hne
    ext j
    have := congrFun h0 j
    simp only [α, Pi.zero_apply] at this
    by_cases h1 : j ∈ S <;> by_cases h2 : j ∈ S' <;> simp_all
  · intro j
    simp only [α]
    by_cases h1 : j ∈ S <;> by_cases h2 : j ∈ S' <;> simp [h1, h2]
  · simp only [α, Finset.sum_sub_distrib, Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.univ_inter]
    rw [hc]; simp
  · funext i
    simp only [α, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, ite_mul, one_mul,
      zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, Pi.zero_apply]
    rw [sub_eq_zero]
    exact congrFun hsum i

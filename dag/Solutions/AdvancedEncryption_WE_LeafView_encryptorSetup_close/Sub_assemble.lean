import SigabaNeoStd.Lattices.Trapdoor.Family.Joint
import SigabaNeoStd.Lattices.LeftoverHash
import Definitions.Def_WE_EncryptorSetup
import Theorems.Thm_AdvancedEncryption_WE_LeafView_trapdoorLaw_flood_close

namespace SmoothAux

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
open scoped ENNReal Matrix

theorem tsum_pi_prod' {α : Type} (g : α → ℝ≥0∞) : ∀ k : ℕ,
    ∑' v : Fin k → α, ∏ i, g (v i) = (∑' a, g a) ^ k
  | 0 => by simp
  | k + 1 => by
    rw [← (Fin.consEquiv fun _ => α).tsum_eq, tsum_prod']
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp only [ENNReal.tsum_mul_left, tsum_pi_prod' g k, ENNReal.tsum_mul_right, pow_succ]
    ring

variable {n m q ℓ : ℕ}

open Classical in
/-- The nonzero integer vectors orthogonal to the kernel of `B`, weighted. -/
noncomputable def orthMass (B : Matrix (Fin n) (Fin m) (ZMod q)) (τ : ℝ) : ℝ≥0∞ :=
  ∑' v : Fin m → ℤ, if v ≠ 0 ∧ Orth B v then wt τ q v else 0

/-- Index of block `i`, column `j`. -/
def idx (i : Fin ℓ) (j : Fin m) : Fin (ℓ * m + m) := Fin.castAdd m (finProdFinEquiv (i, j))

/-- Index of the `W` column `j`. -/
def idxW (j : Fin m) : Fin (ℓ * m + m) := Fin.natAdd (ℓ * m) j

theorem sum_split {R : Type} [AddCommMonoid R] (z : Fin (ℓ * m + m) → R) :
    ∑ k, z k = ∑ i : Fin ℓ, ∑ j : Fin m, z (idx i j) + ∑ j : Fin m, z (idxW j) := by
  rw [Fin.sum_univ_add]
  congr 1
  rw [← Fintype.sum_prod_type', ← finProdFinEquiv.sum_comp]
  rfl

theorem prod_split {R : Type} [CommMonoid R] (z : Fin (ℓ * m + m) → R) :
    ∏ k, z k = (∏ i : Fin ℓ, ∏ j : Fin m, z (idx i j)) * ∏ j : Fin m, z (idxW j) := by
  rw [Fin.prod_univ_add]
  congr 1
  rw [← Fintype.prod_prod_type', ← finProdFinEquiv.prod_comp]
  rfl

theorem stacked_idx (B : Matrix (Fin n) (Fin m) (ZMod q))
    (W : Matrix (Fin (ℓ * n)) (Fin m) (ZMod q)) (a b : Fin ℓ) (t : Fin n) (j : Fin m) :
    stacked B W (finProdFinEquiv (a, t)) (idx b j) = if a = b then B t j else 0 := by
  have h : (idx b j : Fin (ℓ * m + m)).val < ℓ * m := (finProdFinEquiv (b, j)).isLt
  unfold stacked
  rw [dif_pos h]
  have : (⟨(idx b j).val, h⟩ : Fin (ℓ * m)) = finProdFinEquiv (b, j) := Fin.ext rfl
  rw [this]
  simp [AdvancedEncryption.WE.Assumptions.SuccinctLWE.blockDiag]

theorem stacked_idxW (B : Matrix (Fin n) (Fin m) (ZMod q))
    (W : Matrix (Fin (ℓ * n)) (Fin m) (ZMod q)) (r : Fin (ℓ * n)) (j : Fin m) :
    stacked B W r (idxW j) = W r j := by
  simp [stacked, idxW]

theorem stacked_mulVec (B : Matrix (Fin n) (Fin m) (ZMod q))
    (W : Matrix (Fin (ℓ * n)) (Fin m) (ZMod q)) (z : Fin (ℓ * m + m) → ZMod q)
    (a : Fin ℓ) (t : Fin n) :
    (stacked B W *ᵥ z) (finProdFinEquiv (a, t)) =
      ∑ j, B t j * z (idx a j) + ∑ j, W (finProdFinEquiv (a, t)) j * z (idxW j) := by
  rw [Matrix.mulVec, dotProduct, sum_split]
  congr 1
  · rw [Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [stacked_idx, if_pos rfl]
    · intro b _ hb
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [stacked_idx, if_neg (Ne.symm hb), zero_mul]
    · simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [stacked_idxW]

/-- Assemble a vector of `Z^{ℓm+m}` from its blocks. -/
def joinV (p : (Fin ℓ → Fin m → ℤ) × (Fin m → ℤ)) : Fin (ℓ * m + m) → ℤ := fun k =>
  Fin.addCases (fun k' => p.1 (finProdFinEquiv.symm k').1 (finProdFinEquiv.symm k').2)
    (fun j => p.2 j) k

theorem joinV_idx (p : (Fin ℓ → Fin m → ℤ) × (Fin m → ℤ)) (i : Fin ℓ) (j : Fin m) :
    joinV p (idx i j) = p.1 i j := by
  rw [joinV, idx, Fin.addCases_left, Equiv.symm_apply_apply]

theorem joinV_idxW (p : (Fin ℓ → Fin m → ℤ) × (Fin m → ℤ)) (j : Fin m) :
    joinV p (idxW j) = p.2 j := by
  simp [joinV, idxW]

/-- The block decomposition `Z^{ℓm+m} ≃ (Z^m)^ℓ × Z^m`. -/
def blockEquiv : ((Fin ℓ → Fin m → ℤ) × (Fin m → ℤ)) ≃ (Fin (ℓ * m + m) → ℤ) where
  toFun := joinV
  invFun v := (fun i j => v (idx i j), fun j => v (idxW j))
  left_inv p := by
    obtain ⟨f, g⟩ := p
    simp only [joinV_idx, joinV_idxW]
  right_inv v := by
    funext k
    refine Fin.addCases (fun k' => ?_) (fun j => ?_) k
    · obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k'
      exact joinV_idx _ i j
    · exact joinV_idxW _ j

theorem orth_block [NeZero q] (B : Matrix (Fin n) (Fin m) (ZMod q))
    (W : Matrix (Fin (ℓ * n)) (Fin m) (ZMod q)) (v : Fin (ℓ * m + m) → ℤ)
    (hO : Orth (stacked B W) v) (i : Fin ℓ) : Orth B (fun j => v (idx i j)) := by
  classical
  intro x hx
  have hx' : B *ᵥ (fun j => (x j : ZMod q)) = 0 := hx
  set X : Fin (ℓ * m + m) → ℤ := joinV (fun i' => if i' = i then x else 0, 0) with hX
  have hXk : X ∈ kernel (stacked B W) := by
    show stacked B W *ᵥ (fun k => (X k : ZMod q)) = 0
    funext r
    obtain ⟨⟨a, t⟩, rfl⟩ := finProdFinEquiv.surjective r
    rw [stacked_mulVec]
    simp only [hX, joinV_idx, joinV_idxW, Pi.zero_apply, Int.cast_zero, mul_zero,
      Finset.sum_const_zero, add_zero]
    by_cases ha : a = i
    · subst ha
      simp only [if_true]
      exact congrFun hx' t
    · simp [ha]
  have h := hO X hXk
  rw [sum_split] at h
  simp only [hX, joinV_idx, joinV_idxW, Pi.zero_apply, Int.cast_zero, mul_zero,
    Finset.sum_const_zero, add_zero] at h
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)] at h
  simpa using h

theorem orth_blockW [NeZero q] (B : Matrix (Fin n) (Fin m) (ZMod q))
    (W : Matrix (Fin (ℓ * n)) (Fin m) (ZMod q)) (v : Fin (ℓ * m + m) → ℤ)
    (hO : Orth (stacked B W) v) : Orth W (fun j => v (idxW j)) := by
  classical
  intro x hx
  have hx' : W *ᵥ (fun j => (x j : ZMod q)) = 0 := hx
  set X : Fin (ℓ * m + m) → ℤ := joinV (fun _ => 0, x) with hX
  have hXk : X ∈ kernel (stacked B W) := by
    show stacked B W *ᵥ (fun k => (X k : ZMod q)) = 0
    funext r
    obtain ⟨⟨a, t⟩, rfl⟩ := finProdFinEquiv.surjective r
    rw [stacked_mulVec]
    simp only [hX, joinV_idx, joinV_idxW, Pi.zero_apply, Int.cast_zero, mul_zero,
      Finset.sum_const_zero, zero_add]
    exact congrFun hx' _
  have h := hO X hXk
  rw [sum_split] at h
  simpa [hX, joinV_idx, joinV_idxW] using h

theorem orth_zero {n' m' : ℕ} (B : Matrix (Fin n') (Fin m') (ZMod q)) : Orth B 0 := by
  intro x _; simp

theorem wt_zero {m' : ℕ} (τ : ℝ) : wt τ q (0 : Fin m' → ℤ) = 1 := by
  simp [wt]

theorem wt_eq_prod {m' : ℕ} (τ : ℝ) (v : Fin m' → ℤ) :
    wt τ q v = ∏ i, g1 (Real.pi * τ ^ 2 / (q : ℝ) ^ 2) (v i) := by
  rw [prod_g1]; rfl

open Classical in
noncomputable def orthW {n' m' : ℕ} (B : Matrix (Fin n') (Fin m') (ZMod q)) (τ : ℝ)
    (u : Fin m' → ℤ) : ℝ≥0∞ :=
  if Orth B u then wt τ q u else 0

theorem tsum_orthW {n' m' : ℕ} (B : Matrix (Fin n') (Fin m') (ZMod q)) (τ : ℝ) :
    ∑' u, orthW B τ u = orthMass B τ + 1 := by
  classical
  rw [ENNReal.tsum_eq_add_tsum_ite (0 : Fin m' → ℤ), add_comm]
  congr 1
  · unfold orthMass orthW
    refine tsum_congr fun u => ?_
    by_cases hu : u = 0 <;> simp [hu]
  · simp [orthW, orth_zero, wt_zero]

theorem wt_joinV (τ : ℝ) (p : (Fin ℓ → Fin m → ℤ) × (Fin m → ℤ)) :
    wt τ q (joinV p) = (∏ i, wt τ q (p.1 i)) * wt τ q p.2 := by
  rw [wt_eq_prod, prod_split]
  simp only [joinV_idx, joinV_idxW, wt_eq_prod]

/-- **Block bound.** `Λ^⊥([I_ℓ ⊗ B | W])` contains `Λ^⊥(B)^ℓ ⊕ Λ^⊥(W)`, so its nonzero dual mass is
at most `(1 + mass_B)^ℓ (1 + mass_W) − 1`. -/
theorem dualMassE_stacked_le [NeZero q] (B : Matrix (Fin n) (Fin m) (ZMod q))
    (W : Matrix (Fin (ℓ * n)) (Fin m) (ZMod q)) (τ : ℝ) :
    dualMassE (stacked B W) τ + 1 ≤ (orthMass B τ + 1) ^ ℓ * (orthMass W τ + 1) := by
  classical
  set P : (Fin (ℓ * m + m) → ℤ) → ℝ≥0∞ := fun v =>
    if (∀ i, Orth B (fun j => v (idx i j))) ∧ Orth W (fun j => v (idxW j)) then wt τ q v else 0
    with hP
  have h1 : dualMassE (stacked B W) τ + 1 ≤ ∑' v, P v := by
    refine (add_le_add (dualMassE_le (stacked B W) τ) le_rfl).trans ?_
    conv_rhs => rw [ENNReal.tsum_eq_add_tsum_ite (0 : Fin (ℓ * m + m) → ℤ)]
    refine le_trans (le_of_eq (add_comm _ _)) (add_le_add ?_ (ENNReal.tsum_le_tsum fun v => ?_))
    · rw [hP]; simp only
      rw [if_pos ⟨fun i => orth_zero (q := q) B, orth_zero (q := q) W⟩,
        wt_zero]
    · by_cases hv : v = 0
      · simp [hv]
      · rw [if_neg hv]
        split_ifs with h
        · rw [hP]; simp only
          rw [if_pos ⟨fun i => orth_block B W v h.2 i, orth_blockW B W v h.2⟩]
        · exact zero_le
  have h2 : ∑' v, P v = ∑' p : (Fin ℓ → Fin m → ℤ) × (Fin m → ℤ),
      (∏ i, orthW B τ (p.1 i)) * orthW W τ p.2 := by
    rw [← (blockEquiv (ℓ := ℓ) (m := m)).tsum_eq]
    refine tsum_congr fun p => ?_
    show P (joinV p) = _
    rw [hP]; simp only [joinV_idx, joinV_idxW]
    have hf : ∀ i, (fun j => p.1 i j) = p.1 i := fun i => rfl
    simp only [hf]
    unfold orthW
    by_cases hb : ∀ i, Orth B (p.1 i)
    · by_cases hw : Orth W (fun j => p.2 j)
      · rw [if_pos ⟨hb, hw⟩, if_pos hw, wt_joinV]
        congr 1
        exact Finset.prod_congr rfl fun i _ => by rw [if_pos (hb i)]
      · rw [if_neg (fun h => hw h.2), if_neg hw, mul_zero]
    · rw [if_neg (fun h => hb h.1)]
      push Not at hb
      obtain ⟨i, hi⟩ := hb
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi]), zero_mul]
  rw [h2, tsum_prod'] at h1
  simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right] at h1
  rw [tsum_pi_prod' (orthW B τ) ℓ, tsum_orthW, tsum_orthW] at h1
  exact h1

open Classical in
/-- Summed over all matrices, `orthMass` is small (the count behind `SigabaNeoStd`'s
`sum_dualMassE_le`, for any `n`, `m` and prime `q`). -/
theorem sum_orthMass_le {n' m' : ℕ} [Fact q.Prime] (τ : ℝ) :
    (∑ B : Matrix (Fin n') (Fin m') (ZMod q), orthMass B τ) * (q : ℝ≥0∞) ^ m' ≤
      (q : ℝ≥0∞) ^ m' * (q : ℝ≥0∞) ^ (n' * m') * ∑' u : Fin m' → ℤ, wt1 τ u +
        (q : ℝ≥0∞) ^ n' * (q : ℝ≥0∞) ^ (n' * m') * ∑' v : Fin m' → ℤ, wt τ q v := by
  have hq : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  calc (∑ B : Matrix (Fin n') (Fin m') (ZMod q), orthMass B τ) * (q : ℝ≥0∞) ^ m'
      = ∑' v : Fin m' → ℤ, ((Finset.univ.filter fun B : Matrix (Fin n') (Fin m') (ZMod q) =>
          v ≠ 0 ∧ Orth B v).card * (q : ℝ≥0∞) ^ m') * wt τ q v := by
        unfold orthMass
        rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable),
          ← ENNReal.tsum_mul_right]
        refine tsum_congr fun v => ?_
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑' v : Fin m' → ℤ, ((q : ℝ≥0∞) ^ m' * (q : ℝ≥0∞) ^ (n' * m') *
          (if (fun i => (v i : ZMod q)) = 0 ∧ v ≠ 0 then wt τ q v else 0) +
          (q : ℝ≥0∞) ^ n' * (q : ℝ≥0∞) ^ (n' * m') * wt τ q v) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        by_cases hv : v = 0
        · simp [hv]
        have hc := card_orth_le (n := n') (q := q) v
        have hfilt : (Finset.univ.filter fun B : Matrix (Fin n') (Fin m') (ZMod q) =>
            v ≠ 0 ∧ Orth B v) = Finset.univ.filter fun B => Orth B v := by
          ext B; simp [hv]
        rw [hfilt]
        have hc' : ((Finset.univ.filter fun B : Matrix (Fin n') (Fin m') (ZMod q) =>
            Orth B v).card * (q : ℝ≥0∞) ^ m') ≤
            (if (fun i => (v i : ZMod q)) = 0 then (q : ℝ≥0∞) ^ m' * (q : ℝ≥0∞) ^ (n' * m')
              else 0) + (q : ℝ≥0∞) ^ n' * (q : ℝ≥0∞) ^ (n' * m') := by
          have := (Nat.cast_le (α := ℝ≥0∞)).mpr hc
          push_cast at this
          split_ifs at this ⊢ <;> simpa using this
        calc _ ≤ ((if (fun i => (v i : ZMod q)) = 0 then (q : ℝ≥0∞) ^ m' * (q : ℝ≥0∞) ^ (n' * m')
                else 0) + (q : ℝ≥0∞) ^ n' * (q : ℝ≥0∞) ^ (n' * m')) * wt τ q v := by gcongr
          _ = _ := by
            have hiff : ((fun i => (v i : ZMod q)) = 0 ∧ v ≠ 0) ↔ (fun i => (v i : ZMod q)) = 0 :=
              ⟨fun h => h.1, fun h => ⟨h, hv⟩⟩
            simp only [hiff]
            split_ifs <;> simp [add_mul]
    _ = _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ _ := add_le_add_left (mul_le_mul_right (tsum_wt_multiple_le τ) _) _

open Classical in
/-- Markov: few matrices have `orthMass` above `ε`. -/
theorem card_orthMass_gt_le {n' m' : ℕ} [NeZero q] (τ : ℝ) (ε : ℝ≥0∞) :
    ε * (Finset.univ.filter fun B : Matrix (Fin n') (Fin m') (ZMod q) =>
      ε < orthMass B τ).card ≤ ∑ B : Matrix (Fin n') (Fin m') (ZMod q), orthMass B τ := by
  calc ε * ((Finset.univ.filter fun B : Matrix (Fin n') (Fin m') (ZMod q) =>
        ε < orthMass B τ).card : ℝ≥0∞)
      = ∑ _B ∈ Finset.univ.filter fun B : Matrix (Fin n') (Fin m') (ZMod q) =>
          ε < orthMass B τ, ε := by simp [mul_comm]
    _ ≤ ∑ B ∈ Finset.univ.filter fun B : Matrix (Fin n') (Fin m') (ZMod q) =>
          ε < orthMass B τ, orthMass B τ :=
        Finset.sum_le_sum fun B hB => (Finset.mem_filter.mp hB).2.le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => zero_le)

/-- Small block masses give a smooth `[I_ℓ ⊗ B | W]`. -/
theorem dualMassE_stacked_le_half [NeZero q] (B : Matrix (Fin n) (Fin m) (ZMod q))
    (W : Matrix (Fin (ℓ * n)) (Fin m) (ZMod q)) (τ : ℝ) (ε : ℝ≥0∞)
    (hε : (1 + ε) ^ (ℓ + 1) ≤ 3 / 2) (hB : orthMass B τ ≤ ε) (hW : orthMass W τ ≤ ε) :
    dualMassE (stacked B W) τ ≤ 1 / 2 := by
  have h := dualMassE_stacked_le (ℓ := ℓ) B W τ
  have h2 : (orthMass B τ + 1) ^ ℓ * (orthMass W τ + 1) ≤ (1 + ε) ^ (ℓ + 1) := by
    have hB' : orthMass B τ + 1 ≤ 1 + ε := by rw [add_comm 1 ε]; exact add_le_add hB le_rfl
    have hW' : orthMass W τ + 1 ≤ 1 + ε := by rw [add_comm 1 ε]; exact add_le_add hW le_rfl
    rw [pow_succ]
    exact mul_le_mul' (pow_le_pow_left' hB' ℓ) hW'
  have h3 : dualMassE (stacked B W) τ + 1 ≤ 1 / 2 + 1 := by
    refine h.trans (h2.trans (hε.trans (le_of_eq ?_)))
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    have h2i : (2 : ℝ≥0∞)⁻¹ * 2 = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    calc (2 : ℝ≥0∞)⁻¹ * 3 = 2⁻¹ * 1 + 2⁻¹ * 2 := by rw [← mul_add]; norm_num
      _ = _ := by rw [h2i, mul_one]
  exact (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp h3

open Classical in
/-- **Smoothness of `Λ^⊥([I_ℓ ⊗ B | W])` for most `(B, W)`**, counting form. -/
theorem card_bad_stacked_le [Fact q.Prime] (τ : ℝ) (ε : ℝ≥0∞)
    (hε : (1 + ε) ^ (ℓ + 1) ≤ 3 / 2) :
    ε * ((Finset.univ.filter fun p : Matrix (Fin n) (Fin m) (ZMod q) ×
        Matrix (Fin (ℓ * n)) (Fin m) (ZMod q) =>
          (1 / 2 : ℝ≥0∞) < dualMassE (stacked p.1 p.2) τ).card : ℝ≥0∞) * (q : ℝ≥0∞) ^ m ≤
      (q : ℝ≥0∞) ^ (n * m) * (q : ℝ≥0∞) ^ (ℓ * n * m) *
        (2 * (q : ℝ≥0∞) ^ m * ∑' u : Fin m → ℤ, wt1 τ u +
          ((q : ℝ≥0∞) ^ n + (q : ℝ≥0∞) ^ (ℓ * n)) * ∑' v : Fin m → ℤ, wt τ q v) := by
  have hq : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  set SB := Finset.univ.filter fun B : Matrix (Fin n) (Fin m) (ZMod q) => ε < orthMass B τ
  set SW := Finset.univ.filter fun W : Matrix (Fin (ℓ * n)) (Fin m) (ZMod q) => ε < orthMass W τ
  have hsub : (Finset.univ.filter fun p : Matrix (Fin n) (Fin m) (ZMod q) ×
        Matrix (Fin (ℓ * n)) (Fin m) (ZMod q) =>
          (1 / 2 : ℝ≥0∞) < dualMassE (stacked p.1 p.2) τ) ⊆
      SB ×ˢ Finset.univ ∪ Finset.univ ×ˢ SW := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true, true_and, SB, SW,
      Finset.mem_filter]
    by_contra h
    push Not at h
    exact absurd (dualMassE_stacked_le_half p.1 p.2 τ ε hε h.1 h.2) (not_le.mpr hp)
  have hcardB : Fintype.card (Matrix (Fin n) (Fin m) (ZMod q)) = q ^ (n * m) := by
    show Fintype.card (Fin n → Fin m → ZMod q) = _
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]; rw [← pow_mul, mul_comm]
  have hcardW : Fintype.card (Matrix (Fin (ℓ * n)) (Fin m) (ZMod q)) = q ^ (ℓ * n * m) := by
    show Fintype.card (Fin (ℓ * n) → Fin m → ZMod q) = _
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]; rw [← pow_mul, mul_comm]
  have hc : ((Finset.univ.filter fun p : Matrix (Fin n) (Fin m) (ZMod q) ×
        Matrix (Fin (ℓ * n)) (Fin m) (ZMod q) =>
          (1 / 2 : ℝ≥0∞) < dualMassE (stacked p.1 p.2) τ).card : ℝ≥0∞) ≤
      (SB.card : ℝ≥0∞) * (q : ℝ≥0∞) ^ (ℓ * n * m) + (q : ℝ≥0∞) ^ (n * m) * SW.card := by
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
      hcardB, hcardW] at this
    exact_mod_cast this
  have hB := card_orthMass_gt_le (n' := n) (m' := m) (q := q) τ ε
  have hW := card_orthMass_gt_le (n' := ℓ * n) (m' := m) (q := q) τ ε
  have sB := sum_orthMass_le (n' := n) (m' := m) (q := q) τ
  have sW := sum_orthMass_le (n' := ℓ * n) (m' := m) (q := q) τ
  set Q : ℝ≥0∞ := (q : ℝ≥0∞)
  set S1 := ∑' u : Fin m → ℤ, wt1 τ u
  set S2 := ∑' v : Fin m → ℤ, wt τ q v
  calc ε * ((Finset.univ.filter fun p : Matrix (Fin n) (Fin m) (ZMod q) ×
        Matrix (Fin (ℓ * n)) (Fin m) (ZMod q) =>
          (1 / 2 : ℝ≥0∞) < dualMassE (stacked p.1 p.2) τ).card : ℝ≥0∞) * Q ^ m
      ≤ ε * ((SB.card : ℝ≥0∞) * Q ^ (ℓ * n * m) + Q ^ (n * m) * SW.card) * Q ^ m := by gcongr
    _ = Q ^ (ℓ * n * m) * ((ε * SB.card) * Q ^ m) + Q ^ (n * m) * ((ε * SW.card) * Q ^ m) := by
        ring
    _ ≤ Q ^ (ℓ * n * m) * ((∑ B : Matrix (Fin n) (Fin m) (ZMod q), orthMass B τ) * Q ^ m) +
        Q ^ (n * m) * ((∑ W : Matrix (Fin (ℓ * n)) (Fin m) (ZMod q), orthMass W τ) * Q ^ m) := by
        gcongr
    _ ≤ Q ^ (ℓ * n * m) * (Q ^ m * Q ^ (n * m) * S1 + Q ^ n * Q ^ (n * m) * S2) +
        Q ^ (n * m) * (Q ^ m * Q ^ (ℓ * n * m) * S1 + Q ^ (ℓ * n) * Q ^ (ℓ * n * m) * S2) := by
        gcongr
    _ = _ := by ring

theorem exp_neg_le_quarter {τ : ℝ} (hτ : 1 ≤ τ) : Real.exp (-(Real.pi * τ ^ 2)) ≤ 1 / 4 := by
  have h3 : 3 ≤ Real.pi * τ ^ 2 := by nlinarith [Real.pi_gt_three]
  have he : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hmono : Real.exp (-(Real.pi * τ ^ 2)) ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by linarith)
  have hinv : Real.exp (-3) * Real.exp 3 = 1 := by rw [← Real.exp_add]; simp
  have : Real.exp (-3) ≤ 1 / 4 := by nlinarith [Real.exp_pos (-3)]
  linarith

/-- `Σ_{u ≠ 0} e^{−π τ² ‖u‖²} ≤ 6 m e^{−π τ²}` once `3 m e^{−π τ²} ≤ 1/2`. -/
theorem tsum_wt1_le {m' : ℕ} {τ : ℝ} (hτ : 1 ≤ τ)
    (hm : 3 * Real.exp (-(Real.pi * τ ^ 2)) * m' ≤ 1 / 2) :
    ∑' u : Fin m' → ℤ, wt1 τ u ≤ ENNReal.ofReal (6 * Real.exp (-(Real.pi * τ ^ 2)) * m') := by
  set R := Real.exp (-(Real.pi * τ ^ 2)) with hR
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hR4 : R ≤ 1 / 4 := exp_neg_le_quarter hτ
  have hx0 : 0 ≤ Real.pi * τ ^ 2 := by positivity
  have hA : ∑' k : ℤ, g1 (Real.pi * τ ^ 2) k ≤ ENNReal.ofReal (1 + 3 * R) := by
    refine le_trans (tsum_g1_le_large hx0) ?_
    rw [geom_eq hR0 (by linarith)]
    exact ENNReal.ofReal_le_ofReal (ratio_le hR0 hR4)
  have hpow : (∑' k : ℤ, g1 (Real.pi * τ ^ 2) k) ^ m' ≤ ENNReal.ofReal (1 + 6 * R * m') := by
    refine le_trans (pow_le_pow_left' hA _) ?_
    rw [← ENNReal.ofReal_pow (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    have := one_add_pow_le (x := 3 * R) (by linarith) m' (by linarith)
    linarith
  have hZ : ∑' u : Fin m' → ℤ, wt1 τ u + 1 ≤ ENNReal.ofReal (6 * R * m') + 1 := by
    rw [tsum_wt1_add_one, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) (by norm_num),
      add_comm (6 * R * m')]
    exact hpow
  exact ENNReal.le_of_add_le_add_right ENNReal.one_ne_top hZ

/-- `Σ_v e^{−π τ² ‖v‖²/q²} ≤ (4q/τ)^m` once `2τ ≤ q`. -/
theorem tsum_wt_le {m' : ℕ} {τ : ℝ} (hτ : 0 < τ) (hq : (0 : ℝ) < q) (h2 : 2 * τ ≤ q) :
    ∑' v : Fin m' → ℤ, wt τ q v ≤ ENNReal.ofReal ((4 * q / τ) ^ m') := by
  set c := Real.sqrt Real.pi * τ / q with hcdef
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hc0 : 0 < c := by positivity
  have hc2 : Real.pi * τ ^ 2 / (q : ℝ) ^ 2 = c ^ 2 := by
    rw [hcdef, div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
  have hc1 : c ≤ 1 := by
    have hsp : Real.sqrt Real.pi ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt Real.pi_le_four
    rw [hcdef, div_le_one hq]; nlinarith
  set R := Real.exp (-c) with hRdef
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hR1 : R < 1 := by rw [hRdef]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hsub := one_sub_exp_neg_ge hc0.le hc1
  have hreal : Real.exp (1 / 4) * ((1 + R) / (1 - R)) ≤ 4 * q / τ := by
    have hr : (1 + R) / (1 - R) ≤ 4 / c := by
      rw [div_le_div_iff₀ (by linarith) hc0]; nlinarith
    have he := exp_quarter_le_sqrt_pi
    calc Real.exp (1 / 4) * ((1 + R) / (1 - R)) ≤ Real.sqrt Real.pi * (4 / c) := by
          gcongr
      _ = 4 * q / τ := by rw [hcdef]; field_simp
  have hA : ∑' k : ℤ, g1 (Real.pi * τ ^ 2 / (q : ℝ) ^ 2) k ≤ ENNReal.ofReal (4 * q / τ) := by
    rw [hc2]
    refine le_trans tsum_g1_le_small ?_
    rw [geom_eq hR0 hR1, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal hreal
  rw [tsum_wt_eq, ENNReal.ofReal_pow (by positivity)]
  exact pow_le_pow_left' hA _

open Classical in
/-- **Smoothness of `Λ^⊥([I_ℓ ⊗ B | W])` for most uniform `(B, W)`**, explicit form: at most a
`4(ℓ+1)(12 m e^{−πτ²} + (q^n + q^{ℓn}) (4/τ)^m)` fraction of the pairs has nonzero dual mass above
`1/2` at width `τ`, when `q` is prime, `τ ≥ 1`, `2τ ≤ q` and `3 m e^{−πτ²} ≤ 1/2`. -/
theorem card_bad_stacked_explicit [Fact q.Prime] {τ : ℝ} (hτ : 1 ≤ τ) (h2 : 2 * τ ≤ q)
    (hm : 3 * Real.exp (-(Real.pi * τ ^ 2)) * m ≤ 1 / 2) :
    ((Finset.univ.filter fun p : Matrix (Fin n) (Fin m) (ZMod q) ×
        Matrix (Fin (ℓ * n)) (Fin m) (ZMod q) =>
          (1 / 2 : ℝ≥0∞) < dualMassE (stacked p.1 p.2) τ).card : ℝ≥0∞) ≤
      (q : ℝ≥0∞) ^ (n * m) * (q : ℝ≥0∞) ^ (ℓ * n * m) *
        ENNReal.ofReal (4 * (ℓ + 1) * (12 * Real.exp (-(Real.pi * τ ^ 2)) * m +
          ((q : ℝ) ^ n + (q : ℝ) ^ (ℓ * n)) * (4 / τ) ^ m)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hτ0 : 0 < τ := by linarith
  set x : ℝ := 1 / (4 * (ℓ + 1)) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x * ((ℓ + 1 : ℕ) : ℝ) = 1 / 4 := by rw [hx]; push_cast; field_simp
  set ε : ℝ≥0∞ := ENNReal.ofReal x
  have hε : (1 + ε) ^ (ℓ + 1) ≤ 3 / 2 := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) hx0,
      ← ENNReal.ofReal_pow (by positivity)]
    have := one_add_pow_le hx0 (ℓ + 1) (by rw [hx1]; norm_num)
    calc ENNReal.ofReal ((1 + x) ^ (ℓ + 1)) ≤ ENNReal.ofReal (3 / 2) :=
          ENNReal.ofReal_le_ofReal (by rw [hx1] at this; linarith)
      _ = 3 / 2 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  have H := card_bad_stacked_le (n := n) (m := m) (ℓ := ℓ) (q := q) τ ε hε
  set R := Real.exp (-(Real.pi * τ ^ 2))
  set X : ℝ := 12 * R * m + ((q : ℝ) ^ n + (q : ℝ) ^ (ℓ * n)) * (4 / τ) ^ m
  set C : ℝ≥0∞ := ((Finset.univ.filter fun p : Matrix (Fin n) (Fin m) (ZMod q) ×
        Matrix (Fin (ℓ * n)) (Fin m) (ZMod q) =>
          (1 / 2 : ℝ≥0∞) < dualMassE (stacked p.1 p.2) τ).card : ℝ≥0∞)
  set Q : ℝ≥0∞ := (q : ℝ≥0∞)
  have hQ : Q = ENNReal.ofReal q := by simp [Q]
  have hS : 2 * Q ^ m * ∑' u : Fin m → ℤ, wt1 τ u +
      (Q ^ n + Q ^ (ℓ * n)) * ∑' v : Fin m → ℤ, wt τ q v ≤ Q ^ m * ENNReal.ofReal X := by
    calc _ ≤ 2 * Q ^ m * ENNReal.ofReal (6 * R * m) +
          (Q ^ n + Q ^ (ℓ * n)) * ENNReal.ofReal ((4 * q / τ) ^ m) := by
          gcongr
          · exact tsum_wt1_le hτ hm
          · exact tsum_wt_le hτ0 hq0 h2
      _ = Q ^ m * ENNReal.ofReal X := by
          rw [hQ, ← ENNReal.ofReal_pow hq0.le, ← ENNReal.ofReal_pow hq0.le,
            ← ENNReal.ofReal_pow hq0.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
            show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          simp only [X, div_pow, mul_pow]
          field_simp
          ring
  have hQ0 : Q ^ m ≠ 0 := pow_ne_zero _ (by simp [Q, (Fact.out : q.Prime).ne_zero])
  have hQt : Q ^ m ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have H2 : ε * C * Q ^ m ≤ (Q ^ (n * m) * Q ^ (ℓ * n * m) * ENNReal.ofReal X) * Q ^ m := by
    refine H.trans ?_
    calc _ ≤ Q ^ (n * m) * Q ^ (ℓ * n * m) * (Q ^ m * ENNReal.ofReal X) := by gcongr
      _ = _ := by ring
  have H3 : ε * C ≤ Q ^ (n * m) * Q ^ (ℓ * n * m) * ENNReal.ofReal X :=
    (ENNReal.mul_le_mul_iff_left hQ0 hQt).mp H2
  have hinv : ENNReal.ofReal (4 * (ℓ + 1)) * ε = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), hx]
    rw [mul_one_div_cancel (by positivity), ENNReal.ofReal_one]
  calc C = ENNReal.ofReal (4 * (ℓ + 1)) * (ε * C) := by rw [← mul_assoc, hinv, one_mul]
    _ ≤ ENNReal.ofReal (4 * (ℓ + 1)) * (Q ^ (n * m) * Q ^ (ℓ * n * m) * ENNReal.ofReal X) := by
        gcongr
    _ = _ := by
        rw [show ENNReal.ofReal (4 * ((ℓ : ℝ) + 1) * X) =
          ENNReal.ofReal (4 * ((ℓ : ℝ) + 1)) * ENNReal.ofReal X from
            ENNReal.ofReal_mul (by positivity)]
        ring

end SmoothAux

namespace AsmAux

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
  AdvancedEncryption.WE.EncryptorSetup
open scoped ENNReal Matrix

theorem sum_bits (x : ℕ) : ∀ k : ℕ, ∑ t : Fin k, 2 ^ t.val * (x / 2 ^ t.val % 2) = x % 2 ^ k
  | 0 => by simp [Nat.mod_one]
  | k + 1 => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [sum_bits x k, Nat.mod_pow_succ]

theorem bits_mem {r k q : ℕ} (v : Fin r → ZMod q) (j : Fin (r * k)) :
    0 ≤ bits (k := k) v j ∧ bits (k := k) v j ≤ 1 := by
  unfold bits
  constructor
  · positivity
  · have := Nat.mod_lt ((v (finProdFinEquiv.symm j).1).val / 2 ^ (finProdFinEquiv.symm j).2.val)
      (show 2 > 0 by norm_num)
    omega

theorem gadget_bits {r k q : ℕ} [NeZero q] (hq : q ≤ 2 ^ k) (v : Fin r → ZMod q) :
    AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget r k q *ᵥ
      (fun j => ((bits (k := k) v j : ℤ) : ZMod q)) = v := by
  funext i
  rw [Matrix.mulVec, dotProduct, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type,
    Finset.sum_eq_single i]
  · have hv : (v i).val % 2 ^ k = (v i).val :=
      Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt (v i)) hq)
    have h := congrArg (fun z : ℕ => (z : ZMod q)) (sum_bits (v i).val k)
    simp only [hv, ZMod.natCast_zmod_val] at h
    rw [← h, Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget, bits,
      Equiv.symm_apply_apply, if_true, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
  · intro b _ hb
    refine Finset.sum_eq_zero fun t _ => ?_
    simp [AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget, hb]
  · simp

section W
variable {q : ℕ} [NeZero q] {r k mb m : ℕ}

/-- `(A, V) ↦ [A | H − V]` is a bijection. -/
def wEquiv (hm : mb + r * k = m) :
    (Matrix (Fin r) (Fin mb) (ZMod q) × (Fin (r * k) → Fin r → ZMod q)) ≃
      Matrix (Fin r) (Fin m) (ZMod q) where
  toFun p := Wof hm p.1 p.2
  invFun W := (fun i a => W i ⟨a.val, by have := a.isLt; omega⟩,
    fun c i => AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget r k q i c -
      W i ⟨mb + c.val, by have := c.isLt; omega⟩)
  left_inv p := by
    obtain ⟨A, V⟩ := p
    ext i a
    · simp [Wof]
    · simp [Wof]
  right_inv W := by
    ext i j
    simp only [Wof]
    split_ifs with h
    · rfl
    · have : (⟨mb + (j.val - mb), by have := j.isLt; omega⟩ : Fin m) = j := by
        ext; simp; omega
      simp [this]

/-- The law of `W = [A | H − A R]`, with `A R` given by its columns. -/
noncomputable def genW (hm : mb + r * k = m) : PMF (Matrix (Fin r) (Fin m) (ZMod q)) :=
  (PMF.uniformOfFintype (Matrix (Fin r) (Fin mb) (ZMod q))).bind fun A =>
    (Cslib.Probability.PMF.pi fun _ : Fin (r * k) =>
      (PMF.uniformOfFintype (Fin mb → Bool)).map (binaryHash A)).bind fun V =>
        PMF.pure (Wof hm A V)

/-- **`W` with a gadget trapdoor is close to uniform** (leftover hash lemma). -/
theorem closeTo_genW (hm : mb + r * k = m) (hmb : 0 < mb) :
    CloseTo (genW (q := q) hm) (PMF.uniformOfFintype (Matrix (Fin r) (Fin m) (ZMod q)))
      (ENNReal.ofReal ((r * k : ℕ) * (Real.sqrt ((q : ℝ) ^ r * (2 ^ mb : ℝ)⁻¹) / 2))) := by
  classical
  have : Nonempty (Fin mb) := ⟨⟨0, hmb⟩⟩
  have h := closeTo_binaryHash_bind (R := ZMod q) (rr := Fin r) (mm := Fin mb) (I := Fin (r * k))
    (fun A V => PMF.pure (Wof hm A V))
  have hideal : ((PMF.uniformOfFintype (Matrix (Fin r) (Fin mb) (ZMod q))).bind fun A =>
      (Cslib.Probability.PMF.pi fun _ : Fin (r * k) =>
        PMF.uniformOfFintype (Fin r → ZMod q)).bind fun V => PMF.pure (Wof hm A V)) =
      PMF.uniformOfFintype (Matrix (Fin r) (Fin m) (ZMod q)) := by
    rw [Cslib.Probability.PMF.pi_uniformOfFintype,
      ← Cslib.Probability.PMF.uniformOfFintype_map_equiv (wEquiv (q := q) hm),
      ← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.map_bind]
    congr 1; funext A
    rw [PMF.map_comp]
    rfl
  unfold genW
  rw [← hideal]
  convert h using 2
  simp [ZMod.card]

theorem sum_split_m {R : Type} [AddCommMonoid R] (hm : mb + r * k = m) (f : Fin m → R) :
    ∑ j, f j = ∑ a : Fin mb, f ⟨a.val, by have := a.isLt; omega⟩ +
      ∑ c : Fin (r * k), f ⟨mb + c.val, by have := c.isLt; omega⟩ := by
  rw [← (finCongr hm).sum_comp, Fin.sum_univ_add]
  rfl

theorem Wof_dOf (hm : mb + r * k = m) (hq : q ≤ 2 ^ k) (A : Matrix (Fin r) (Fin mb) (ZMod q))
    (Rc : Fin (r * k) → Fin mb → Bool) (v : Fin r → ZMod q) :
    Wof hm A (fun c => binaryHash A (Rc c)) *ᵥ (fun j => ((dOf hm Rc v j : ℤ) : ZMod q)) = v := by
  classical
  conv_rhs => rw [← gadget_bits (r := r) hq v]
  funext i
  rw [Matrix.mulVec, dotProduct, sum_split_m hm, Matrix.mulVec, dotProduct]
  have h1 : ∀ a : Fin mb, Wof hm A (fun c => binaryHash A (Rc c)) i
      ⟨a.val, by have := a.isLt; omega⟩ = A i a := by
    intro a; simp [Wof]
  have h2 : ∀ c : Fin (r * k), Wof hm A (fun c => binaryHash A (Rc c)) i
      ⟨mb + c.val, by have := c.isLt; omega⟩ =
        AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget r k q i c -
          binaryHash A (Rc c) i := by
    intro c
    simp only [Wof]
    rw [dif_neg (by simp)]
    simp only [Nat.add_sub_cancel_left]
  have h3 : ∀ a : Fin mb, dOf hm Rc v ⟨a.val, by have := a.isLt; omega⟩ =
      ∑ c, (if Rc c a then bits (k := k) v c else 0) := by
    intro a; simp [dOf]
  have h4 : ∀ c : Fin (r * k), dOf hm Rc v ⟨mb + c.val, by have := c.isLt; omega⟩ =
      bits (k := k) v c := by
    intro c
    simp only [dOf]
    rw [dif_neg (by simp)]
    simp only [Nat.add_sub_cancel_left]
  simp only [h1, h2, h3, h4]
  simp only [binaryHash, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
  have h5 : ∑ a : Fin mb, A i a * ((∑ c, (if Rc c a then bits (k := k) v c else 0) : ℤ) : ZMod q) =
      ∑ c : Fin (r * k), (∑ a, A i a * bitVal (Rc c a)) * ((bits (k := k) v c : ℤ) : ZMod q) := by
    simp only [Int.cast_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    by_cases h : Rc c a <;> simp [h, bitVal]
  rw [h5]
  ring

omit [NeZero q] in
theorem abs_dOf_le (hm : mb + r * k = m) (Rc : Fin (r * k) → Fin mb → Bool)
    (v : Fin r → ZMod q) (j : Fin m) : |dOf hm Rc v j| ≤ ((r * k : ℕ) : ℤ) := by
  classical
  unfold dOf
  split_ifs with h
  · have h0 : 0 ≤ ∑ c, (if Rc c ⟨j.val, h⟩ then bits (k := k) v c else 0) :=
      Finset.sum_nonneg fun c _ => by split_ifs <;> [exact (bits_mem v c).1; exact le_rfl]
    rw [abs_of_nonneg h0]
    calc ∑ c, (if Rc c ⟨j.val, h⟩ then bits (k := k) v c else 0) ≤ ∑ _c : Fin (r * k), (1 : ℤ) :=
          Finset.sum_le_sum fun c _ => by split_ifs <;> [exact (bits_mem v c).2; norm_num]
      _ = (r * k : ℕ) := by simp
  · have hb := bits_mem (k := k) v ⟨j.val - mb, by have := j.isLt; omega⟩
    rw [abs_of_nonneg hb.1]
    have : 1 ≤ r * k := by have := j.isLt; omega
    calc _ ≤ (1 : ℤ) := hb.2
      _ ≤ _ := by exact_mod_cast this

end W

end AsmAux


namespace AsmAux

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
  AdvancedEncryption.WE.EncryptorSetup
open scoped ENNReal Matrix

open Classical in
theorem unif_toOuterMeasure {α : Type} [Fintype α] [Nonempty α] (P : α → Prop) :
    (PMF.uniformOfFintype α).toOuterMeasure {a | P a} =
      ((Finset.univ.filter P).card : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Cslib.Probability.PMF.uniformOfFintype_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem genW_eq {q r k mb m : ℕ} [NeZero q] (hm : mb + r * k = m) :
    genW (q := q) hm = (PMF.uniformOfFintype (Matrix (Fin r) (Fin mb) (ZMod q))).bind fun A =>
      (Cslib.Probability.PMF.pi fun _ : Fin (r * k) => PMF.uniformOfFintype (Fin mb → Bool)).map
        fun Rc => Wof hm A fun c => binaryHash A (Rc c) := by
  unfold genW
  congr 1; funext A
  rw [Cslib.Probability.PMF.pi_map, PMF.bind_map]
  rfl

end AsmAux

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
  AdvancedEncryption.WE.EncryptorSetup
open scoped ENNReal

open Classical in
theorem solution (p : Params) [Fact p.q.Prime] (mb : ℕ) (hm : mb + p.ℓ * p.n * p.k = p.m)
    (hmb : 0 < mb) (hσ : (0 : ℝ) < p.σ) (hσ1 : (1 : ℝ) ≤ p.σ) (h2 : 2 * (p.σ : ℝ) ≤ p.q)
    (hexp : 3 * Real.exp (-(Real.pi * (p.σ : ℝ) ^ 2)) * p.m ≤ 1 / 2)
    (hrad : (p.σ : ℝ) * Real.sqrt (p.ℓ * p.m + p.m : ℕ) + (p.ℓ * p.n * p.k : ℕ) ≤
      (p.σ : ℝ) * (p.ℓ * p.m + p.m : ℕ)) :
    CloseTo (encLaw p mb hm hσ) (chalLaw p)
      ((p.ℓ * (p.n * p.k) : ℕ) * (ENNReal.ofReal (2 * (Real.pi * (p.ℓ * p.m + p.m : ℕ) *
          (((p.ℓ * p.n * p.k : ℕ) : ℝ) ^ 2 + 2 * ((p.σ : ℝ) * (p.ℓ * p.m + p.m : ℕ)) *
            (p.ℓ * p.n * p.k : ℕ)) / (p.σ : ℝ) ^ 2)) +
        ((p.ℓ * p.m + p.m : ℕ) : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ (p.ℓ * p.m + p.m)) +
        ENNReal.ofReal (3 * 2 ^ (p.ℓ * p.m + p.m) * (1 / 4) ^ ((p.ℓ * p.m + p.m) ^ 2))) +
      ENNReal.ofReal (4 * (p.ℓ + 1) * (12 * Real.exp (-(Real.pi * (p.σ : ℝ) ^ 2)) * p.m +
          ((p.q : ℝ) ^ p.n + (p.q : ℝ) ^ (p.ℓ * p.n)) * (4 / (p.σ : ℝ)) ^ p.m)) +
      2 * ENNReal.ofReal ((p.ℓ * p.n * p.k : ℕ) *
        (Real.sqrt ((p.q : ℝ) ^ (p.ℓ * p.n) * (2 ^ mb : ℝ)⁻¹) / 2))) := by
  have hq0 : NeZero p.q := ⟨(Fact.out : p.q.Prime).ne_zero⟩
  have hqk : p.q ≤ 2 ^ p.k := Nat.le_pow_clog one_lt_two _
  set Wf : Matrix (Fin (p.ℓ * p.n)) (Fin mb) (ZMod p.q) → (Fin (p.ℓ * p.n * p.k) → Fin mb → Bool) →
      Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q) :=
    fun A Rc => Wof hm A fun c => binaryHash A (Rc c) with hWf
  set μ := (PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind fun B =>
    (PMF.uniformOfFintype (Matrix (Fin (p.ℓ * p.n)) (Fin mb) (ZMod p.q))).bind fun A =>
      (Cslib.Probability.PMF.pi fun _ : Fin (p.ℓ * p.n * p.k) =>
        PMF.uniformOfFintype (Fin mb → Bool)).map fun Rc => (B, A, Rc) with hμ
  set f := fun x : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin (p.ℓ * p.n)) (Fin mb) (ZMod p.q) ×
      (Fin (p.ℓ * p.n * p.k) → Fin mb → Bool) =>
    (floodT p hσ x.1 (Wf x.2.1 x.2.2) (dOf hm x.2.2)).map fun T => (x.1, Wf x.2.1 x.2.2, T) with hf
  set g := fun x : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin (p.ℓ * p.n)) (Fin mb) (ZMod p.q) ×
      (Fin (p.ℓ * p.n * p.k) → Fin mb → Bool) =>
    (trapdoorLaw p x.1 (Wf x.2.1 x.2.2)).map fun T => (x.1, Wf x.2.1 x.2.2, T) with hg
  set good := fun x : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin (p.ℓ * p.n)) (Fin mb) (ZMod p.q) ×
      (Fin (p.ℓ * p.n * p.k) → Fin mb → Bool) =>
    dualMassE (stacked x.1 (Wf x.2.1 x.2.2)) p.σ ≤ 1 / 2 with hgood
  have henc : encLaw p mb hm hσ = μ.bind f := by
    simp only [hμ, hf, PMF.bind_bind, PMF.bind_map]
    rfl
  -- step 1: flooding, outside the non-smooth event
  have hstep1 := closeTo_bind_good μ f g good fun x _ hx =>
    (AdvancedEncryption.WE.LeafView.trapdoorLaw_flood_close p hσ hσ1 x.1 (Wf x.2.1 x.2.2)
      (dOf hm x.2.2) (AsmAux.Wof_dOf hm hqk x.2.1 x.2.2) (p.ℓ * p.n * p.k)
      (AsmAux.abs_dOf_le hm x.2.2) hrad hx).map fun T => (x.1, Wf x.2.1 x.2.2, T)
  set LHL := ENNReal.ofReal ((p.ℓ * p.n * p.k : ℕ) *
        (Real.sqrt ((p.q : ℝ) ^ (p.ℓ * p.n) * (2 ^ mb : ℝ)⁻¹) / 2)) with hLHL
  have hW := AsmAux.closeTo_genW (q := p.q) (r := p.ℓ * p.n) (k := p.k) hm hmb
  -- the joint law of `(B, W)` in the encryptor
  have hjoint : μ.map (fun x => (x.1, Wf x.2.1 x.2.2)) =
      (PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind fun B =>
        (AsmAux.genW (q := p.q) (r := p.ℓ * p.n) (k := p.k) hm).map fun W => (B, W) := by
    rw [AsmAux.genW_eq]
    simp only [hμ, PMF.map_bind, PMF.map_comp]
    rfl
  -- step 2: the bad event
  have hbad : ev μ (fun x => ind (¬ good x)) ≤
      ENNReal.ofReal (4 * (p.ℓ + 1) * (12 * Real.exp (-(Real.pi * (p.σ : ℝ) ^ 2)) * p.m +
          ((p.q : ℝ) ^ p.n + (p.q : ℝ) ^ (p.ℓ * p.n)) * (4 / (p.σ : ℝ)) ^ p.m)) + LHL := by
    have hcount := SmoothAux.card_bad_stacked_explicit (n := p.n) (m := p.m) (q := p.q)
      (ℓ := p.ℓ) hσ1 h2 hexp
    have hcardB : Fintype.card (Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) = p.q ^ (p.n * p.m) := by
      show Fintype.card (Fin p.n → Fin p.m → ZMod p.q) = _
      simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]; rw [← pow_mul, mul_comm]
    have hcardW : Fintype.card (Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q)) =
        p.q ^ (p.ℓ * p.n * p.m) := by
      show Fintype.card (Fin (p.ℓ * p.n) → Fin p.m → ZMod p.q) = _
      simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]; rw [← pow_mul, mul_comm]
    have hunif : ((PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind fun B =>
        (PMF.uniformOfFintype (Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))).map fun W =>
          (B, W)) = PMF.uniformOfFintype _ :=
      Cslib.Probability.PMF.uniformOfFintype_prod _ _
    calc ev μ (fun x => ind (¬ good x))
        = μ.toOuterMeasure {x | ¬ good x} := by rw [toOuterMeasure_eq_ev]; congr
      _ = (μ.map fun x => (x.1, Wf x.2.1 x.2.2)).toOuterMeasure
            {y | ¬ dualMassE (stacked y.1 y.2) p.σ ≤ 1 / 2} := by
          rw [PMF.toOuterMeasure_map_apply]; rfl
      _ ≤ ((PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind fun B =>
            (PMF.uniformOfFintype (Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))).map fun W =>
              (B, W)).toOuterMeasure {y | ¬ dualMassE (stacked y.1 y.2) p.σ ≤ 1 / 2} + LHL := by
          rw [hjoint]
          exact (CloseTo.bind_right _ fun B _ => hW.map fun W => (B, W)) _
      _ ≤ _ := by
          refine add_le_add ?_ le_rfl
          rw [hunif, AsmAux.unif_toOuterMeasure, Fintype.card_prod, hcardB, hcardW]
          simp only [not_le]
          rw [← div_eq_mul_inv]
          apply ENNReal.div_le_of_le_mul
          push_cast
          exact le_trans (le_of_eq rfl) (hcount.trans (le_of_eq (mul_comm _ _)))
  -- step 3: `W` with a trapdoor replaced by a uniform `W`
  have hg_eq : μ.bind g = (PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind
      fun B => (AsmAux.genW (q := p.q) (r := p.ℓ * p.n) (k := p.k) hm).bind fun W =>
        (trapdoorLaw p B W).map fun T => (B, W, T) := by
    rw [AsmAux.genW_eq]
    simp only [hμ, hg, PMF.bind_bind, PMF.bind_map]
    rfl
  have hstep3 : CloseTo (μ.bind g) (chalLaw p) LHL := by
    rw [hg_eq]
    exact CloseTo.bind_right _ fun B _ => hW.bind_left fun W => (trapdoorLaw p B W).map fun T => (B, W, T)
  rw [henc]
  refine (hstep1.trans hstep3).mono ?_
  calc _ ≤ _ + (ENNReal.ofReal (4 * (p.ℓ + 1) * (12 * Real.exp (-(Real.pi * (p.σ : ℝ) ^ 2)) * p.m +
          ((p.q : ℝ) ^ p.n + (p.q : ℝ) ^ (p.ℓ * p.n)) * (4 / (p.σ : ℝ)) ^ p.m)) + LHL) + LHL := by
        gcongr
    _ = _ := by ring


import Mathlib.LinearAlgebra.Matrix.Rank

private theorem triangular_budget {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hd : ∀ i, A i i ≠ 0)
    (bad : Finset (Fin n)) (hb : ∀ i j, j < i → A i j ≠ 0 → i ∈ bad) :
    n ≤ A.rank + bad.card := by
  classical
  let good := Finset.univ \ bad
  let M := A.submatrix (fun i : good => i.val) (fun i : good => i.val)
  have tri : M.IsUpperTriangular := by
    intro i j h
    by_contra ne
    exact (Finset.mem_sdiff.mp i.property).2 (hb i j h ne)
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular tri]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hd i.val)
  have hr := A.rank_submatrix_le (fun i : good => i.val) (fun i : good => i.val)
  change M.rank ≤ _ at hr
  rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_coe] at hr
  have hc : good.card + bad.card = n := by
    simpa [good] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)
  omega

private theorem single_seed {K : Type*} [Field K] [DecidableEq K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hd : ∀ i, A i i ≠ 0) :
    2*n ≤ 2*A.rank +
      (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ A p.1 p.2 ≠ 0)).card := by
  classical
  let L := Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1 ∧ A p.1 p.2 ≠ 0)
  let U := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ A p.1 p.2 ≠ 0)
  have hl := triangular_budget A hd (L.image Prod.fst) (by
    intro i j h ne
    exact Finset.mem_image.mpr ⟨(i,j), by simp [L,h,ne], rfl⟩)
  have hu := triangular_budget A.transpose hd (U.image Prod.snd) (by
    intro i j h ne
    exact Finset.mem_image.mpr ⟨(j,i), by simpa [U,h] using ne, rfl⟩)
  rw [Matrix.rank_transpose] at hu
  have dl : Disjoint L U := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [L,U,Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact (not_lt_of_gt hp.1) hq.1
  have join : L ∪ U = Finset.univ.filter
      (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ A p.1 p.2 ≠ 0) := by
    ext p
    simp only [L,U,Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h,ne⟩|⟨h,ne⟩)
      · exact ⟨h.ne',ne⟩
      · exact ⟨h.ne,ne⟩
    · rintro ⟨hne,ne⟩
      rcases lt_or_gt_of_ne hne with h|h
      · exact Or.inr ⟨h,ne⟩
      · exact Or.inl ⟨h,ne⟩
  rw [← join, Finset.card_union_of_disjoint dl]
  have h₁ : (L.image Prod.fst).card ≤ L.card := Finset.card_image_le
  have h₂ : (U.image Prod.snd).card ≤ U.card := Finset.card_image_le
  omega

theorem solution {K : Type*} [Field K] [DecidableEq K] {n s r c : ℕ}
    (A : Fin s → Matrix (Fin n) (Fin n) K)
    (hd : ∀ t i, A t i i ≠ 0) (hr : ∀ t, (A t).rank ≤ r)
    (hc : ∀ i j, i ≠ j → (Finset.univ.filter (fun t => A t i j ≠ 0)).card ≤ c) :
    2*s*n ≤ 2*s*r + n*(n-1)*c := by
  classical
  let pairs : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  have count (t : Fin s) :
      (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ A t p.1 p.2 ≠ 0)).card =
      ∑ p ∈ pairs, (if A t p.1 p.2 ≠ 0 then 1 else 0 : ℕ) := by
    rw [← Finset.card_filter]
    simp only [pairs, Finset.filter_filter]
  have hp : pairs.card = n*(n-1) := by
    have e : pairs = (Finset.univ : Finset (Fin n)).offDiag := by ext p; simp [pairs]
    simp [e, Finset.offDiag_card, Nat.mul_sub]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin s))) (fun t _ =>
    (single_seed (A t) (hd t)).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hr t)) _))
  simp_rw [count] at hsum
  rw [Finset.sum_add_distrib, Finset.sum_comm] at hsum
  have hcol : (∑ p ∈ pairs, ∑ t : Fin s, (if A t p.1 p.2 ≠ 0 then 1 else 0 : ℕ)) ≤
      ∑ _p ∈ pairs, c := by
    apply Finset.sum_le_sum
    intro p h
    rw [← Finset.card_filter]
    exact hc _ _ (Finset.mem_filter.mp h).2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hp] at *
  nlinarith

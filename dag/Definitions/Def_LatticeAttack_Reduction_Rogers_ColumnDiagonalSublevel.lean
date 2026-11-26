module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRPotential

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Rogers

/-- On a potential sublevel, a common lower bound on squared prefix covolumes bounds
each individual QR diagonal. -/
theorem columnDiagonal_of_prefixLower {n : ℕ} {x : SL n} (a : ColumnCandidate x)
    (h : ∃ L : ℝ, 0 < L ∧ ∀ (c : ColumnCandidate x) (k : ℕ), k ≤ n →
      L ≤ ∏ j : Fin n with j.val < k, c.r j j ^ 2) :
    ∃ D : ℝ, ∀ c : ColumnCandidate x, c.potential ≤ a.potential → ∀ i, c.r i i ≤ D := by
  classical
  obtain ⟨L, hL, hlo⟩ := h
  refine ⟨1 + a.potential / (L * L ^ (n - 1)), ?_⟩
  intro c hc i
  let p (k : ℕ) := ∏ j : Fin n with j.val < k, c.r j j ^ 2
  have hp : c.potential = ∏ t : Fin n, p (t.val + 1) := by
    unfold ColumnCandidate.potential p
    simp_rw [Finset.prod_filter]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    have eq : (Finset.univ.filter fun t : Fin n ↦ j.val < t.val + 1) = Finset.Ici j := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, Nat.lt_succ_iff, Fin.le_def]
    rw [← Finset.prod_filter, eq, Finset.prod_const, Fin.card_Ici]
  have step : p (i.val + 1) = c.r i i ^ 2 * p i.val := by
    have eq : (Finset.univ.filter fun j : Fin n ↦ j.val < i.val + 1) =
        insert i (Finset.univ.filter fun j : Fin n ↦ j.val < i.val) := by
      ext j
      simp [Fin.ext_iff]
      omega
    unfold p
    rw [eq, Finset.prod_insert (by simp)]
  have rest : L ^ (n - 1) ≤ ∏ t ∈ Finset.univ.erase i, p (t.val + 1) := by
    calc
      _ = ∏ _t ∈ Finset.univ.erase i, L := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ ↦ hL.le) (fun t _ ↦ hlo c _ t.isLt)
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left (hlo c _ i.isLt.le) (sq_nonneg (c.r i i)))
    rest (pow_nonneg hL.le _) (mul_nonneg (sq_nonneg _) (hL.le.trans (hlo c _ i.isLt.le)))
  rw [hp, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), step] at hc
  have bound : c.r i i ^ 2 ≤ a.potential / (L * L ^ (n - 1)) := by
    apply (le_div_iff₀ (by positivity)).2
    rw [← mul_assoc]
    exact hprod.trans hc
  nlinarith [sq_nonneg (c.r i i - 1)]

end SigabaNeo.Rogers

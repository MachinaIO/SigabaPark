import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRPotential

set_option autoImplicit true

namespace SigabaNeo.Rogers

/-- Preserving the adjacent two-column volume and shrinking its first diagonal
strictly decreases the weighted product of squared QR diagonals. -/
theorem columnSwapPotential_lt {n : ℕ} {x : SL n} (b c : ColumnCandidate x)
    (i j : Fin n) (hij : i.val + 1 = j.val)
    (hsmall : b.r i i ^ 2 < c.r i i ^ 2)
    (harea : b.r i i ^ 2 * b.r j j ^ 2 = c.r i i ^ 2 * c.r j j ^ 2)
    (hrest : ∀ t, t ≠ i → t ≠ j → b.r t t = c.r t t) :
    b.potential < c.potential := by
  classical
  let s := (Finset.univ.erase i).erase j
  let w (a : ColumnCandidate x) (t : Fin n) := (a.r t t ^ 2) ^ (n - t.val)
  have hji : j ≠ i := by intro h; subst j; omega
  have split (a : ColumnCandidate x) :
      a.potential = (w a i * w a j) * ∏ t ∈ s, w a t := by
    change ∏ t, w a t = _
    rw [← Finset.mul_prod_erase Finset.univ (w a) (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) (w a) (by simp [hji] : j ∈ _)]
    exact (mul_assoc _ _ _).symm
  have rest : ∏ t ∈ s, w b t = ∏ t ∈ s, w c t := by
    apply Finset.prod_congr rfl
    intro t ht
    simp only [s, Finset.mem_erase, Finset.mem_univ, and_true] at ht
    simp [w, hrest t ht.2 ht.1]
  rw [split b, split c, rest]
  apply mul_lt_mul_of_pos_right _ (Finset.prod_pos fun t _ ↦
    pow_pos (sq_pos_of_pos (c.positive t)) _)
  have exponent : n - i.val = n - j.val + 1 := by omega
  have pair (a : ColumnCandidate x) : w a i * w a j =
      (a.r i i ^ 2 * a.r j j ^ 2) ^ (n - j.val) * a.r i i ^ 2 := by
    simp only [w, exponent, pow_succ, mul_pow]
    ring
  rw [pair b, pair c, harea]
  exact mul_lt_mul_of_pos_left hsmall (pow_pos
    (mul_pos (sq_pos_of_pos (c.positive i)) (sq_pos_of_pos (c.positive j))) _)

end SigabaNeo.Rogers

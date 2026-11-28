import Definitions.Def_PacketTraceBasis
import Mathlib.Tactic

theorem solution {F : Type*} [Field F] (S : ℕ) (hs : 0 < S) (a : ℕ → F)
    (alpha omega : F) (ho : IsPrimitiveRoot omega S) :
    (∑ i ∈ Finset.range S, ∑ j ∈ Finset.range S, a j * (alpha * omega ^ i) ^ j) =
      (S : F) * a 0 := by
  rw [Finset.sum_comm]
  have term (j : ℕ) :
      (∑ i ∈ Finset.range S, a j * (alpha * omega ^ i) ^ j) =
        a j * alpha ^ j * ∑ i ∈ Finset.range S, (omega ^ j) ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, ← pow_mul, Nat.mul_comm i j, pow_mul]
    ring
  simp_rw [term]
  rw [Finset.sum_eq_single 0]
  · simp [mul_comm]
  · intro j hj h0
    have hne := ho.pow_ne_one_of_pos_of_lt h0 (Finset.mem_range.mp hj)
    rw [geom_sum_eq hne, ← pow_mul, Nat.mul_comm j S, pow_mul, ho.pow_eq_one]
    simp
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hs))

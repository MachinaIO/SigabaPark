import Mathlib
open Finset

theorem solution {R : Type*} [CommRing R] (d : ℕ) (z : R) (hz : z^(2^d) = -1)
    (k : ℕ) (hk : 0 < k) (hmax : k < 2^(d+1)) :
    ∑ i ∈ range (2^(d+1)), (z^k)^i = 0 := by
  have split (m : ℕ) (x : R) : (∑ i ∈ range (m+m), x^i) =
      (1+x^m) * (∑ i ∈ range m, x^i) := by
    rw [sum_range_add]
    simp only [pow_add, ← mul_sum]
    ring
  induction d generalizing k z with
  | zero =>
    have h : k=1 := by norm_num at hmax; omega
    subst k
    simp_all [sum_range_succ]
  | succ d ih =>
    have size : 2^(d+1+1) = 2^(d+1)+2^(d+1) := by rw [pow_succ]; omega
    rw [size, split]
    obtain ⟨a, ha | ha⟩ := Nat.even_or_odd' k
    · subst k
      have hz2 : (z^2)^(2^d) = -1 := by rw [←pow_mul, Nat.mul_comm, ← pow_succ]; exact hz
      have small : a < 2^(d+1) := by omega
      have h := ih (z^2) hz2 a (by omega) small
      rw [pow_mul, h, mul_zero]
    · subst k
      have ho : (z^(2*a+1))^(2^(d+1)) = -1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hz]
        simp [pow_add, pow_mul]
      rw [ho]
      simp

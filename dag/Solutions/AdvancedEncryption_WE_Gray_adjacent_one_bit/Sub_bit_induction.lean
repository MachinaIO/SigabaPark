import Mathlib

theorem solution (t : ℕ) :
    ∃ j : ℕ, (t ^^^ t / 2) ^^^ ((t + 1) ^^^ (t + 1) / 2) = 2 ^ j := by
  have gray_bit : ∀ (b : Bool) (m : ℕ),
      Nat.bit b m ^^^ Nat.bit b m / 2 = Nat.bit (b ^^ m.bodd) (m ^^^ m / 2) := by
    intro b m
    rw [Nat.bit_div_two]
    conv_lhs => arg 2; rw [← Nat.bit_bodd_div2 m]
    rw [Nat.xor_bit, Nat.div2_val]
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    obtain ⟨b, m, rfl⟩ : ∃ b m, t = Nat.bit b m := ⟨t.bodd, t.div2, (Nat.bit_bodd_div2 t).symm⟩
    cases b with
    | false =>
      refine ⟨0, ?_⟩
      have h1 : Nat.bit false m + 1 = Nat.bit true m := by
        simp only [Nat.bit_val, Bool.toNat_true, Bool.toNat_false]
      rw [h1, gray_bit, gray_bit, Nat.xor_bit, Nat.xor_self]
      cases m.bodd <;> rfl
    | true =>
      have hm : m < Nat.bit true m := by
        simp only [Nat.bit_val, Bool.toNat_true]; omega
      obtain ⟨j, hj⟩ := ih m hm
      refine ⟨j + 1, ?_⟩
      have h1 : Nat.bit true m + 1 = Nat.bit false (m + 1) := by
        simp only [Nat.bit_val, Bool.toNat_true, Bool.toNat_false]; omega
      rw [h1, gray_bit, gray_bit, Nat.xor_bit, hj, Nat.bodd_succ]
      cases m.bodd <;> simp [Nat.bit_val, pow_succ, mul_comm]

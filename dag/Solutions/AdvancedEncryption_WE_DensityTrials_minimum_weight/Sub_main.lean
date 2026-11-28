import Definitions.Def_DensityTrials

open AdvancedEncryption.WE.DensityTrials

theorem solution {n d : Nat} (f : Table n) (h : Low d f) (positive : 0 < weight f) :
    2^n ≤ weight f * 2^d := by
  have diff : ∀ {k} (a b : Table k),
      (weight (delta a b) = 0 ↔ a = b) ∧ weight (delta a b) ≤ weight a + weight b := by
    intro k a
    induction a with
    | leaf a => intro b; cases b with | leaf b => cases a <;> cases b <;> decide
    | fork a b ia ib =>
      intro c
      cases c with
      | fork c e =>
        obtain ⟨h1,h2⟩ := ia c
        obtain ⟨h3,h4⟩ := ib e
        simp only [delta, weight, Nat.add_eq_zero_iff, Table.fork.injEq, h1, h3]
        exact ⟨trivial, by omega⟩
  induction n generalizing d with
  | zero =>
    cases f with
    | leaf b =>
      cases b with
      | false => simp [weight] at positive
      | true => simpa [weight] using (Nat.one_le_two_pow (n := d))
  | succ k ih =>
    cases f with
    | fork a b =>
      by_cases eq : a = b
      · subst b
        have ha : Low d a := by
          cases d with
          | zero => exact h.2
          | succ d => exact h.1
        have pos : 0 < weight a := by simp only [weight] at positive; omega
        have hrec := ih a ha pos
        simp only [weight, pow_succ, Nat.add_mul]
        omega
      · cases d with
        | zero => exact False.elim (eq h.1)
        | succ e =>
          have nz : 0 < weight (delta a b) := Nat.pos_of_ne_zero (fun hz => eq ((diff _ _).1.mp hz))
          have hrec := ih (delta a b) h.2 nz
          have hle := Nat.mul_le_mul_right (2^e) (diff a b).2
          simp only [weight, Nat.pow_succ, ← Nat.mul_assoc]
          omega

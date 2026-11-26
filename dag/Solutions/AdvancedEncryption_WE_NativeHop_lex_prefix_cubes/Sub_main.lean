import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

theorem solution (w k : ℕ) :
    w < k ↔ ∃ j, k.testBit j = true ∧ w.testBit j = false ∧
      ∀ i, j < i → w.testBit i = k.testBit i := by
  constructor
  · intro hwk
    have hne : w ≠ k := by omega
    have hex : ∃ i, w.testBit i ≠ k.testBit i := by
      by_contra h
      simp only [ne_eq, not_exists, not_not] at h
      exact hne (Nat.eq_of_testBit_eq h)
    -- bits above k agree (both false)
    have hbound : ∀ i, k ≤ i → w.testBit i = k.testBit i := by
      intro i hi
      have hk : k < 2 ^ i := lt_of_le_of_lt hi (Nat.lt_two_pow_self)
      have hw : w < 2 ^ i := lt_trans hwk hk
      rw [Nat.testBit_eq_false_of_lt hk, Nat.testBit_eq_false_of_lt hw]
    classical
    let P : ℕ → Prop := fun i => w.testBit i ≠ k.testBit i
    obtain ⟨i0, hi0⟩ := hex
    have hi0k : i0 ≤ k := by
      by_contra h
      exact hi0 (hbound i0 (by omega))
    set j := Nat.findGreatest P k with hj
    have hPj : P j := Nat.findGreatest_spec (P := P) hi0k hi0
    have habove : ∀ i, j < i → w.testBit i = k.testBit i := by
      intro i hi
      by_cases hik : i ≤ k
      · by_contra h
        have := Nat.le_findGreatest (P := P) hik h
        omega
      · exact hbound i (by omega)
    refine ⟨j, ?_, ?_, habove⟩
    · cases hk : k.testBit j
      · exfalso
        cases hw : w.testBit j
        · exact hPj (by rw [hw, hk])
        · have : k < w := Nat.lt_of_testBit j hk hw (fun i hi => (habove i hi).symm)
          omega
      · rfl
    · cases hw : w.testBit j
      · rfl
      · exfalso
        cases hk : k.testBit j
        · have : k < w := Nat.lt_of_testBit j hk hw (fun i hi => (habove i hi).symm)
          omega
        · exact hPj (by rw [hw, hk])
  · rintro ⟨j, hk, hw, hab⟩
    exact Nat.lt_of_testBit j hw hk hab

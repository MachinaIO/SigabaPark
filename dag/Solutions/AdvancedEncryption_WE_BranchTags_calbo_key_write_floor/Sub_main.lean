import Mathlib.Data.Nat.Basic

theorem solution
    (tagBits rows columns coeffBits clock : ℕ)
    (ht : 7 ≤ tagBits) (hn : 256 ≤ rows) (hc : 32768 ≤ columns) (hb : 128 ≤ coeffBits)
    (hwrite : 2 * tagBits * rows * columns * coeffBits ≤ clock) :
    15032385536 ≤ clock := by
  calc
    15032385536 = 2 * 7 * 256 * 32768 * 128 := by decide
    _ ≤ 2 * tagBits * rows * columns * coeffBits :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ ht) hn) hc) hb
    _ ≤ clock := hwrite

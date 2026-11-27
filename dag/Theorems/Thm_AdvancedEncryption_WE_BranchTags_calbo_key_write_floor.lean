import Mathlib.Data.Nat.Basic

theorem AdvancedEncryption.WE.BranchTags.calbo_key_write_floor
    (tagBits rows columns coeffBits clock : ℕ)
    (ht : 7 ≤ tagBits) (hn : 256 ≤ rows) (hc : 32768 ≤ columns) (hb : 128 ≤ coeffBits)
    (hwrite : 2 * tagBits * rows * columns * coeffBits ≤ clock) :
    15032385536 ≤ clock := by sorry

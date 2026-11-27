import Mathlib

theorem AdvancedEncryption.WE.BranchTags.dense_gate_write_floor
    (rows dim width bits clock : ℕ) (hn : 256 ≤ rows) (hd : 128 ≤ dim)
    (hw : 256 ≤ width) (hb : 21 ≤ bits)
    (hwrite : 4096 * rows * (dim + width) * bits ≤ clock) :
    8455716864 ≤ clock := by sorry

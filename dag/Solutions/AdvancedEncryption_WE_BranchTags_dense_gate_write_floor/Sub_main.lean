import Mathlib

theorem solution
    (rows dim width bits clock : ℕ) (hn : 256 ≤ rows) (hd : 128 ≤ dim)
    (hw : 256 ≤ width) (hb : 21 ≤ bits)
    (hwrite : 4096 * rows * (dim + width) * bits ≤ clock) :
    8455716864 ≤ clock := by
  calc
    8455716864 = 4096 * 256 * (128 + 256) * 21 := by decide
    _ ≤ 4096 * rows * (dim + width) * bits := by gcongr
    _ ≤ clock := hwrite

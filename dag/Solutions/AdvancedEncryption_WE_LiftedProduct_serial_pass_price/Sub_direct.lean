import Mathlib

theorem solution :
    let T : ℕ := 24320+3968
    let table : ℕ := 4*4096*(4*512+1)
    let full (w : ℕ) := 17*512*w + 512*w + 512*8
    2^32 < table+T*full 17 ∧ 2^32 < table+T*full 16 ∧
    2^32 < table+T*(78848+32*32*32*13) ∧
    table+T*78848 = 2264023040 := by
  norm_num

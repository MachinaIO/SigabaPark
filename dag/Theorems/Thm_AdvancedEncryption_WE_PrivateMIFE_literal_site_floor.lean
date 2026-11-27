import Mathlib

theorem AdvancedEncryption.WE.PrivateMIFE.literal_site_floor (ys : List ℕ) (k : ℕ) (hn : ys.length = k)
    (hw : ys.sum + 1 = 128 + k) :
    31744 ≤ (ys.map (fun y ↦ 2 ^ y)).sum + 2 ^ k := by sorry

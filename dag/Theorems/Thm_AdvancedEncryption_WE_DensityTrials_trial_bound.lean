import Mathlib.Tactic

theorem AdvancedEncryption.WE.DensityTrials.trial_bound (n d t : Nat) (w : Nat) (_hw : w ≤ 2 ^ n)
    (hd : 2 ^ n ≤ w * 2 ^ d)
    (ht : (2 ^ d - 1) ^ t * 2 ^ 127 ≤ (2 ^ d) ^ t) :
    (2 ^ n - w) ^ t * 2 ^ 127 ≤ (2 ^ n) ^ t := by sorry

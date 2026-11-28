import Mathlib

theorem AdvancedEncryption.WE.PrefixTag.AlternatingWires (v : Nat → Int) (score : Nat → Int) (initial : score 0 = 1-v 0-v 1)
    (pairStep : ∀ i, score (i+1) =
      score i + (v (2*i+2) + v (2*i+1) - 1) +
                (1-v (2*i+2)-v (2*i+3))) (k : Nat) :
    score k = 1-v 0-v (2*k+1) := by sorry

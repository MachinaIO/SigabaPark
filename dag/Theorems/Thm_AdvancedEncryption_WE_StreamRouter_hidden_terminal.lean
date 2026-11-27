import Mathlib

theorem AdvancedEncryption.WE.StreamRouter.hidden_terminal (key pad other msg : Bool) :
    xor (xor (!key) (!pad)) other = xor (xor key pad) other ∧ xor (!msg) (!key) = xor msg key := by sorry

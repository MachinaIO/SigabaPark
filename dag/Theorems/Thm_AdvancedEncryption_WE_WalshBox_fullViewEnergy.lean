import Definitions.Def_NandWalshBox
open NandWalshBox
theorem AdvancedEncryption.WE.WalshBox.fullViewEnergy {X S : Type} [Fintype X] [Fintype S] (d : X → ℝ)
    (c : S → ℝ) (b : ℝ)
    (h : ∑ x, (d x)^2 = (Fintype.card X : ℝ) * ∑ i, (c i)^2)
    (hc : ∀ i, (c i)^2 ≤ b^2) :
    (∑ x, |d x|)^2 ≤ (Fintype.card X : ℝ)^2 * (Fintype.card S : ℝ) * b^2 := by sorry

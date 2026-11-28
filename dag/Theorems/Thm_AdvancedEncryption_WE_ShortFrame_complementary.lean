import Definitions.Def_ShortNand

open SigabaNeo ShortNand

theorem AdvancedEncryption.WE.ShortFrame.complementary {ι : Type} [Fintype ι] (v : ι→ℤ) (b : ℤ) (hv : ∑ i,(v i)^2 ≤ 2*b) :
    (∑ i,(v i/2)^2) ≤ b ∨ (∑ i,(v i-v i/2)^2) ≤ b := by sorry

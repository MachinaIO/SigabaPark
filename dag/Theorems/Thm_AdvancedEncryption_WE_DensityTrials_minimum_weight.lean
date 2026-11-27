import Definitions.Def_DensityTrials

open AdvancedEncryption.WE.DensityTrials

theorem AdvancedEncryption.WE.DensityTrials.minimum_weight {n d : Nat} (f : Table n) (h : Low d f) (positive : 0 < weight f) :
    2^n ≤ weight f * 2^d := by sorry

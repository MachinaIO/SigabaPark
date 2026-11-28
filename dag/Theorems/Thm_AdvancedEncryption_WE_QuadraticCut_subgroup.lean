import Definitions.Def_QuadraticNandCut
open AffineNandCut
open scoped BigOperators
theorem AdvancedEncryption.WE.QuadraticCut.subgroup {I G T : Type*} [Fintype I] [Fintype G] [AddCommMonoid G] [AddCommMonoid T]
    (p : I→G) (f : I→G→+T) (off : ∀ i j, i≠j → f i (p j)=0)
    (on : ∀ i, f i (p i)≠0) :
    2^Fintype.card I ≤ Fintype.card G := by sorry

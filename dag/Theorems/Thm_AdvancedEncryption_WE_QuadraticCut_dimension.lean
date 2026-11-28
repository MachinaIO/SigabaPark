import Definitions.Def_QuadraticNandCut
open AffineNandCut
open scoped BigOperators
theorem AdvancedEncryption.WE.QuadraticCut.dimension {F I J : Type*} [Field F] [Fintype I] [Fintype J]
    [DecidableEq I] (P : Matrix I J F) (Q : Matrix J I F) (d : I→F) (hd : ∀i,d i≠0)
    (h : ∀i j,(P*Q) i j=if i=j then d i else 0) :
    Fintype.card I ≤ Fintype.card J := by sorry

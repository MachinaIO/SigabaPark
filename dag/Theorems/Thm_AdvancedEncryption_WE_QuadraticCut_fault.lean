import Definitions.Def_QuadraticNandCut
open AffineNandCut
open scoped BigOperators
theorem AdvancedEncryption.WE.QuadraticCut.fault (l r : Bool) (h : (l || r)=true) :
    ∀ t : Bool, ∃ x y : Bool, ((x && y) ^^ ((l || x) && (r || y)))=t := by sorry

import Definitions.Def_QuadraticNandCut
open AffineNandCut
open scoped BigOperators
theorem AdvancedEncryption.WE.QuadraticCut.shear (x u y v : Bool) :
    ((x && y) ^^ (u && v)) = (((x ^^ u) && y) ^^ (u && (y ^^ v))) := by sorry

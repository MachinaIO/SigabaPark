import Definitions.Def_OwnedGarbling

open OwnedGarbling
open scoped BigOperators

theorem AdvancedEncryption.WE.OwnedGarbling.affine_decode {I : Type} [Fintype I] (theta pi a r : I → ZMod 2) (c s : ZMod 2) :
    c + (∑ i, pi i * (a i + r i)) + s =
    (c + ∑ i, theta i * a i) + (∑ i, (theta i + pi i) * (a i + r i)) +
      (s + ∑ i, theta i * r i) := by sorry

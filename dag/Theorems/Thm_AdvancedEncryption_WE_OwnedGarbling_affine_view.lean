import Definitions.Def_OwnedGarbling

open OwnedGarbling
open scoped BigOperators

theorem AdvancedEncryption.WE.OwnedGarbling.affine_view {I : Type} [Fintype I] [DecidableEq I] (slope pad point : I → ZMod 2)
    (offset : ZMod 2) (test : ZMod 2 → (I → ZMod 2) → ℝ) :
    (∑ inactive : I → ZMod 2,
       test (offset + ∑ i, (pad i + point i * (pad i + inactive i)))
         (fun i ↦ slope i + pad i + inactive i)) =
    ∑ delta : I → ZMod 2,
      test ((offset + ∑ i, point i * slope i) + ∑ i, pad i + ∑ i, point i * delta i)
        delta := by sorry

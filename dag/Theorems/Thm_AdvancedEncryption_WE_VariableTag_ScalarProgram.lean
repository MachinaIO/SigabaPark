import Definitions.Def_VariableLocalReplay
open VariableLocalReplay VariableTagFront
theorem AdvancedEncryption.WE.VariableTag.ScalarProgram (gs : List (Nat × Nat)) (xs : List Bool) (last : Bool) (h : Bytes gs) :
    ((activeProgram xs gs).isSome = true ↔ Backward xs.length gs) ∧
    (Backward xs.length gs → activeProgram xs gs =
      some ((gs.foldl SigabaNeo.estep (xs,last)).1)) := by sorry

import Definitions.Def_OwnedGarbling

open OwnedGarbling
open scoped BigOperators

theorem AdvancedEncryption.WE.OwnedGarbling.whole_graph (st : Nat → Wire) (net : List Gate) :
    (fun i ↦ ((net.foldl emit st) i).ref) =
      net.foldl publicStep (fun i ↦ (st i).ref) := by sorry

import Definitions.Def_WE_GKW_Trace

namespace AdvancedEncryption.WE.TraceLamp

/-- Read both sources against the registered history before appending the claimed bit. -/
def samples (w : List Bool) : SigabaNeo.GateList → List Bool → List (Bool × Bool × Bool)
  | g :: gs, z :: zs =>
      (w.getD g.1 true, w.getD g.2 true, z) :: samples (w ++ [z]) gs zs
  | _, _ => []

end AdvancedEncryption.WE.TraceLamp

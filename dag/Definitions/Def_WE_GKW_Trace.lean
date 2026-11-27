import SigabaNeoStd.Machines.Gates

namespace AdvancedEncryption.WE.GKW

/-- Every supplied gate bit agrees with its NAND on the previously available wires. -/
def TraceFits (w : List Bool) : SigabaNeo.GateList → List Bool → Prop
  | [], [] => True
  | g :: gs, v :: vs =>
    v = !(w.getD g.1 true && w.getD g.2 true) ∧ TraceFits (w ++ [v]) gs vs
  | _, _ => False

end AdvancedEncryption.WE.GKW

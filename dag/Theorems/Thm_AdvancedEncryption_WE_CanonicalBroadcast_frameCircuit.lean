import Definitions.Def_CanonBroadcastRoles

open BroadcastWire SigabaNeo Turing.MultiTapeTM AdvancedEncryption.WE.CircuitSAT

theorem AdvancedEncryption.WE.CanonicalBroadcast.frameCircuit (n s : Nat) (g : Circuit n s) :
    frame ((relation n s).encStmt g) =
       (g.gates.flatMap (fun p => List.replicate (8*p.1+3) true++[false]++
         List.replicate (4*p.2+1) true++[false]))++[false] := by sorry

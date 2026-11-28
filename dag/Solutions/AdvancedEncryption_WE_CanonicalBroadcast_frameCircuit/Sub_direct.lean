import Definitions.Def_CanonBroadcastRoles

open BroadcastWire SigabaNeo Turing.MultiTapeTM AdvancedEncryption.WE.CircuitSAT

theorem solution (n s : Nat) (g : Circuit n s) :
    frame ((relation n s).encStmt g) =
       (g.gates.flatMap (fun p => List.replicate (8*p.1+3) true++[false]++
         List.replicate (4*p.2+1) true++[false]))++[false] := by
  change frame (encGates g.gates)=_
  suffices h : ∀ l : GateList, stuff (encGates l)= l.flatMap (fun p => List.replicate (8*p.1+3) true++[false]++List.replicate (4*p.2+1) true++[false]) by
    rw [frame',h]
  intro l
  induction l with
  | nil => rfl
  | cons p ps ih =>
    change stuff (frame (encGate p) ++ encGates ps) = _
    rw [stuff_append,two,ih,List.flatMap_cons]

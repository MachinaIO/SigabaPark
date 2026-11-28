import Definitions.Def_CanonBroadcastRoles

open BroadcastWire SigabaNeo Turing.MultiTapeTM AdvancedEncryption.WE.CircuitSAT

theorem AdvancedEncryption.WE.CanonicalBroadcast.swapping (gs hs : GateList)
    (h : List.Forall₂ (fun (p q : Nat×Nat) => p=q ∨ p=q.swap) gs hs) (w : List Bool) :
    evalGates (w,gs) = evalGates (w,hs) := by sorry

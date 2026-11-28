import Definitions.Def_CanonBroadcastRoles

open BroadcastWire SigabaNeo Turing.MultiTapeTM AdvancedEncryption.WE.CircuitSAT

theorem solution (a b : Nat) :
    ¬ ((8*a+3=3 ∧ 4*b+1=7) ∨ (8*a+3=7 ∧ 4*b+1=3)) := by omega

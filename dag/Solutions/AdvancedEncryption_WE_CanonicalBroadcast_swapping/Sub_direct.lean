import Definitions.Def_CanonBroadcastRoles

open BroadcastWire SigabaNeo Turing.MultiTapeTM AdvancedEncryption.WE.CircuitSAT

theorem solution (gs hs : GateList)
    (h : List.Forall₂ (fun (p q : Nat×Nat) => p=q ∨ p=q.swap) gs hs) (w : List Bool) :
    evalGates (w,gs) = evalGates (w,hs) := by
  suffices ∀ st : List Bool × Bool, gs.foldl estep st=hs.foldl estep st by
    exact congrArg Prod.snd (this _)
  induction h with
  | nil => simp
  | @cons p q gs hs same _ ih =>
    intro st
    rcases same with rfl|rfl
    · exact ih _
    · simp only [List.foldl_cons]
      have step_eq : estep st q.swap = estep st q := by
        rcases q with ⟨a,b⟩;rcases st with ⟨v,t⟩;simp [estep,Bool.and_comm]
      rw [step_eq];exact ih _

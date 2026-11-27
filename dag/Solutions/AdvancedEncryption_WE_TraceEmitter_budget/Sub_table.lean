import Definitions.Def_WE_TraceEmitter

open SigabaNeo AdvancedEncryption.WE.TraceEmitter

theorem solution :
    machine.Deterministic ∧ machine.time = 484513167 ∧ machine.descLen = 88452 ∧ machine.cost < 2^32 := by
  have hs : machine.states = 26 := by
    change Nat.card Phase = _
    rw [Nat.card_eq_fintype_card]
    decide
  refine ⟨Machine.deterministic_ofTM _ _, rfl, ?_, ?_⟩
  all_goals
    simp only [Machine.cost, Machine.descLen, hs]
    decide

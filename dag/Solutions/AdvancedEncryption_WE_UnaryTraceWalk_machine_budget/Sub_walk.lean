import Definitions.Def_WE_UnaryTraceWalk

open SigabaNeo Turing AdvancedEncryption.WE AdvancedEncryption.WE.UnaryTraceWalk

theorem solution :
    machine.Deterministic ∧ machine.time = 173064452 ∧ machine.descLen = 5728050 ∧
      machine.cost < 2 ^ 32 := by
  refine ⟨Machine.deterministic_ofTM _ _, rfl, ?_, ?_⟩
  all_goals
    have hs : machine.states = 4243 := by
      change Nat.card (Fin 4224 ⊕ Phase) = _
      rw [Nat.card_sum, Nat.card_fin, Nat.card_eq_fintype_card]
      decide
    simp only [Machine.cost, Machine.descLen, hs]
    decide

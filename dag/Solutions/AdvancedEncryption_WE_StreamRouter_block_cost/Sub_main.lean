import Definitions.Def_StreamedRouterBlock

open StreamedRouterBlock
theorem solution : machine.time = 51380 ∧ machine.descLen = 426065508 ∧ machine.Deterministic ∧
    SharedQuarterBlock.machine.time = 51941 ∧ SharedQuarterBlock.machine.descLen = 168276528 ∧
    SharedQuarterBlock.machine.Deterministic := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_⟩ <;> unfold SigabaNeo.Machine.Deterministic <;> intro q a w o <;> rfl

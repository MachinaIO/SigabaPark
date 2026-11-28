import Definitions.Def_TwoTraceEnergy
import Mathlib.Tactic

theorem TwoTraceEnergy.registeredRun (g : SigabaNeo.GateList) (x : List Bool) :
    (∃ y : List Bool, TwoTraceEnergy.zeroRun g (true :: x) (true :: y) true true) ↔
    SigabaNeo.evalGates (x,g) = true := by
  sorry

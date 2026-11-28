import Definitions.Def_SyndromePhaseGuard
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem SyndromePhaseGuard.dyadicGate :
    ((List.range 256).map SyndromePhaseGuard.weight).sum = 4096 ∧
    ((List.range 4).map (fun j ↦
      (List.range 4).map (SyndromePhaseGuard.marginal j))) =
        List.replicate 4 [1664, 1664, 384, 384] ∧
    ((List.range 256).map (fun x ↦ ((SyndromePhaseGuard.weight x - SyndromePhaseGuard.weight (x ^^^ 170)) +
      (SyndromePhaseGuard.weight (x ^^^ 170) - SyndromePhaseGuard.weight x)))).sum = 7680 := by
  sorry

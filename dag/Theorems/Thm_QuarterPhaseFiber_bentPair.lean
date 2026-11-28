import Definitions.Def_QuarterPhaseFiber
import Mathlib.Tactic

theorem QuarterPhaseFiber.bentPair : ∀ a b : Bool,
    QuarterPhaseFiber.pair a b false false + QuarterPhaseFiber.pair a b false true +
    QuarterPhaseFiber.pair a b true false + QuarterPhaseFiber.pair a b true true =
    2 * QuarterPhaseFiber.sign (a && b) := by
  sorry

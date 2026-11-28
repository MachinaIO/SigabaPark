import Definitions.Def_TwoTraceEnergy
import Mathlib.Tactic

theorem TwoTraceEnergy.independentTrace {V : Type*} {n : ℕ} (a b t : V → Fin n → Bool) :
    (∀ v w, 0 ≤ TwoTraceEnergy.total a b t v w ∧ TwoTraceEnergy.total a b t v w ≤ 6 * n) ∧
    ((∃ v w, TwoTraceEnergy.total a b t v w = 0) ↔ ∃ v, ∀ j, t v j = (a v j && b v j)) := by
  sorry

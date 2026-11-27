import Definitions.Def_WE_OnceTraceScan
open AdvancedEncryption.WE.OnceTrace SigabaNeo
/-- A zero-energy trace exists on a given assignment exactly when the registered gate evaluator accepts. -/
theorem AdvancedEncryption.WE.OnceEnergy.zero_iff_registered (w : List Bool) (gs : GateList) :
    (∃ rows : List ((ℕ × ℕ) × Bool), rows.map Prod.fst = gs ∧
      energy (true::w,true) rows = 0) ↔ evalGates (w,gs) = true := by sorry

import Definitions.Def_ShortNand

open SigabaNeo ShortNand

theorem AdvancedEncryption.WE.ShortFrame.gap (q : ℤ) (hq : 5≤q) (n : ℕ) (gs : GateList) :
    ((∃ x : List Bool, x.length=n ∧ evalGates (x,gs)=true) ↔
      ∃ bs, feasible q n gs bs ∧ energy bs = gs.length) ∧
    (∀ bs, feasible q n gs bs →
      (energy bs = gs.length ∧ ∀ t∈bs,hot t) ∨ (gs.length : ℤ)+2 ≤ energy bs) := by sorry

import Definitions.Def_OrderedNand

open OrderedNand SigabaNeo

theorem AdvancedEncryption.WE.OrderedIdeal.target_witness {n : Nat} (pre : GateList) (g : Nat × Nat) {S : Tags (Fin n)}
    (d : Derives (Inputs n) (issued (n+1) (pre++[g])) (.wire (n+1+pre.length) true) S)
    (clean : consistent S) : ∃ x : Fin n → Bool, evalGates (List.ofFn x,pre++[g]) = true := by sorry

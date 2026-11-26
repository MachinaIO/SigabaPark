import Mathlib.Data.List.Basic

theorem AdvancedEncryption.WE.KSplit.chain_reach_succ {S B : Type} (h : S → B → S) (s0 : S)
    (n : ℕ) (s : S) :
    (∃ ws : List B, ws.length = n + 1 ∧ ws.foldl h s0 = s) ↔
      ∃ s' : S, (∃ ws : List B, ws.length = n ∧ ws.foldl h s0 = s') ∧ ∃ w : B, h s' w = s := by
  sorry

import Definitions.Def_OrderedNand

open OrderedNand

theorem AdvancedEncryption.WE.OrderedIdeal.row_exact (v : Nat → Bool) (h0 : v 0 = true) (d l r : Nat) (y : Key) :
    (∃ p q, row d l r p q y ∧ live v p ∧ live v q) ↔ y = .wire d (!(v l && v r)) := by sorry

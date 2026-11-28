import Definitions.Def_TableauShiftAudit

open TableauShiftAudit

theorem solution {G : Type} [AddGroup G] (n : Nat) (s : (i : Fin n) → History G i.val → G)
    (out : History G n) : ∃! coins : History G n, triangular n s coins = out := by
  exact (triangular n s).bijective.existsUnique out

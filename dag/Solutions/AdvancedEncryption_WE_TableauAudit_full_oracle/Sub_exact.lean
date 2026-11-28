import Definitions.Def_TableauShiftAudit

open TableauFirstFailure

theorem solution {Z : Type} (rows : Z → List Row) (b : Bool)
    (noWitness : ∀ z, (rows z).all Prod.fst = false) :
    (fun z => (!b) ^^ mask (changeFirst (rows z))) = (fun z => b ^^ mask (rows z)) ∧
    (fun z => changeFirst (changeFirst (rows z))) = rows ∧
    ∀ z, (changeFirst (rows z)).map Prod.fst = (rows z).map Prod.fst := by
  refine ⟨?_, funext (fun z => involution (rows z)), fun z => public_checks (rows z)⟩
  funext z
  rw [mask_flip, noWitness z]
  cases b <;> cases mask (rows z) <;> rfl

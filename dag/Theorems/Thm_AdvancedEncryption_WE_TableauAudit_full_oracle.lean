import Definitions.Def_TableauShiftAudit

open TableauFirstFailure

theorem AdvancedEncryption.WE.TableauAudit.full_oracle {Z : Type} (rows : Z → List Row) (b : Bool)
    (noWitness : ∀ z, (rows z).all Prod.fst = false) :
    (fun z => (!b) ^^ mask (changeFirst (rows z))) = (fun z => b ^^ mask (rows z)) ∧
    (fun z => changeFirst (changeFirst (rows z))) = rows ∧
    ∀ z, (changeFirst (rows z)).map Prod.fst = (rows z).map Prod.fst := by
  sorry

import Mathlib

theorem AdvancedEncryption.WE.LegalBranch.FullViewCount {X Y : Type*} [Fintype X] [DecidableEq Y] (e : X ≃ X)
    (view : X → Y) (bit : X → Bool) (v : Y) (b : Bool)
    (hv : ∀ x, view (e x) = view x) (hb : ∀ x, bit (e x) = !bit x) :
    Fintype.card {x : X // view x = v ∧ bit x = b} =
    Fintype.card {x : X // view x = v ∧ bit x = !b} := by sorry

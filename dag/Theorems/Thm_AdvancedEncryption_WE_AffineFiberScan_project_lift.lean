import Definitions.Def_AffineFiberScan

theorem AdvancedEncryption.WE.AffineFiberScan.project_lift {X Y : Type} (source : X → Prop) (domain : X → Prop)
    (child : Y → Prop) (project : X → Y) (lift : Y → X)
    (necessary : ∀ x, source x → domain x)
    (factor : ∀ x, domain x → (source x ↔ child (project x)))
    (inside : ∀ y, domain (lift y)) (section_ : ∀ y, project (lift y) = y) :
    (∀ x, source x → child (project x)) ∧
    (∀ y, child y → source (lift y)) ∧
    ((¬ ∃ x, source x) ↔ ¬ ∃ y, child y) := by sorry

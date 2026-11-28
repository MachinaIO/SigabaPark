import Definitions.Def_ProjectiveJoin
open ProjectiveJoin
theorem AdvancedEncryption.WE.ProjectiveJoin.sharedLift {S C : Type} {X : C → Type} (sOK : S → Prop)
    (ok : (c : C) → S → X c → Prop) (centers : (c : C) → Set (X c))
    (replace : ∀ c s, (∃ z, ok c s z) → ∃ z ∈ centers c,ok c s z) :
    (∃ (s : S) (z : (c : C) → X c), sOK s ∧ ∀ c,ok c s (z c)) ↔
    ∃ (s : S) (z : (c : C) → X c), sOK s ∧ ∀ c,z c ∈ centers c ∧ ok c s (z c) := by sorry

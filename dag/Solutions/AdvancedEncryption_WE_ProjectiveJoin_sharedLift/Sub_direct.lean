import Definitions.Def_ProjectiveJoin
open ProjectiveJoin
theorem solution {S C : Type} {X : C → Type} (sOK : S → Prop)
    (ok : (c : C) → S → X c → Prop) (centers : (c : C) → Set (X c))
    (replace : ∀ c s, (∃ z, ok c s z) → ∃ z ∈ centers c,ok c s z) :
    (∃ (s : S) (z : (c : C) → X c), sOK s ∧ ∀ c,ok c s (z c)) ↔
    ∃ (s : S) (z : (c : C) → X c), sOK s ∧ ∀ c,z c ∈ centers c ∧ ok c s (z c) := by
  classical
  constructor
  · rintro ⟨s,z,hs,hz⟩
    have h (c) := replace c s ⟨z c,hz c⟩
    exact ⟨s,fun c=>Classical.choose (h c),hs,fun c=>Classical.choose_spec (h c)⟩
  · rintro ⟨s,z,hs,hz⟩
    exact ⟨s,z,hs,fun c=>(hz c).2⟩

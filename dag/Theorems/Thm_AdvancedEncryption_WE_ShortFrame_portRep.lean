import Definitions.Def_ShortNand

open SigabaNeo ShortNand

theorem AdvancedEncryption.WE.ShortFrame.portRep {I J : Type} (key : J→I) (p : J→ℤ) (q : ℤ) :
    (∃ s : I→ℤ, ∀ j, eqm q (p j) (s (key j))) ↔
      ∀ j k, key j=key k → eqm q (p j) (p k) := by sorry

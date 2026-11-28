import Definitions.Def_ProjectiveJoin
open ProjectiveJoin
theorem AdvancedEncryption.WE.ProjectiveJoin.planeHits : ∀ a b c d : Fin 7, a ≠ b → a ≠ c → a ≠ d →
    b ≠ c → b ≠ d → c ≠ d → ((omitted a ^^^ omitted b) ^^^ (omitted c ^^^ omitted d)) ≠ 0 := by sorry

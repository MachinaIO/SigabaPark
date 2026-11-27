import Definitions.Def_BKSStarredHybrid

open BKSStarredHybrid

theorem AdvancedEncryption.WE.BKSStar.shared_inner_admissible {I S X W : Type} [DecidableEq I] [Nonempty S]
    (j k : I) (tables : I → S → X → W) (dummy : S → X → W)
    (rows : S → X) (padding : S → W) :
    route k (tables k) (fun s ↦ (rows s, none, padding s)) =
    route k (if k = j then dummy else tables k)
      (fun s ↦ (rows s, some j, tables j s (rows s))) := by sorry

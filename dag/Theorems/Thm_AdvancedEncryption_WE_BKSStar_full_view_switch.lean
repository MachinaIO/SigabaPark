import Definitions.Def_BKSStarredHybrid

open BKSStarredHybrid

theorem AdvancedEncryption.WE.BKSStar.full_view_switch {a r q : Nat} {n : Fin r → Nat}
    (op : Ops) (t : Tables a r q n) (b e : Bool) (j : Fin a)
    (localLaw : PMF (Local a r q n)) (starLaw : PMF (Star r q n)) :
    (localLaw.bind fun o ↦ starLaw.bind fun c ↦ PMF.pure (honestFrame op t b e j o c)) =
    (starLaw.bind fun c ↦ localLaw.bind fun o ↦
      PMF.pure (assemble op t b j o (challenge op t j b e c))) := by sorry

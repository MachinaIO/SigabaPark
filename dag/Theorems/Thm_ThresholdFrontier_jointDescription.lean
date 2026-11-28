import Definitions.Def_ThresholdFrontier

theorem ThresholdFrontier.jointDescription {S I G Q K : Type*} [AddCommGroup G]
    (step : K → S → I → S × G) (first hidden : K → Q → S × G)
    (delta : Q → G) (suffix : Q → List I)
    (sync : ∀ k q, hidden k q = ThresholdFrontier.translate (first k q) (delta q)) :
    (fun k : K => (k, fun q : Q => ThresholdFrontier.walk (step k) (hidden k q) (suffix q))) =
    (fun k : K => (k, fun q : Q =>
      ThresholdFrontier.translate (ThresholdFrontier.walk (step k) (first k q) (suffix q))
        (delta q))) := by
  sorry

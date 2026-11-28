import Definitions.Def_ThresholdFrontier
import Mathlib.Tactic

private theorem commute {S I G : Type*} [AddCommGroup G] (step : S → I → S × G)
    (v : S × G) (g : G) (ds : List I) :
    ThresholdFrontier.walk step (ThresholdFrontier.translate v g) ds =
      ThresholdFrontier.translate (ThresholdFrontier.walk step v ds) g := by
  induction ds generalizing v with
  | nil => rfl
  | cons d ds ih =>
    rcases v with ⟨s, a⟩
    simp only [ThresholdFrontier.walk, ThresholdFrontier.translate]
    rw [show a + g + (step s d).2 = a + (step s d).2 + g by abel]
    exact ih ((step s d).1, a + (step s d).2)

theorem solution {S I G Q K : Type*} [AddCommGroup G]
    (step : K → S → I → S × G) (first hidden : K → Q → S × G)
    (delta : Q → G) (suffix : Q → List I)
    (sync : ∀ k q, hidden k q = ThresholdFrontier.translate (first k q) (delta q)) :
    (fun k : K => (k, fun q : Q => ThresholdFrontier.walk (step k) (hidden k q) (suffix q))) =
    (fun k : K => (k, fun q : Q =>
      ThresholdFrontier.translate (ThresholdFrontier.walk (step k) (first k q) (suffix q))
        (delta q))) := by
  funext k
  congr 1
  funext q
  rw [sync]
  apply commute

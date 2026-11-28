import Mathlib.Algebra.Group.Basic

namespace ThresholdFrontier

def translate {S G : Type*} [Add G] (v : S × G) (g : G) : S × G :=
  (v.1, v.2 + g)

def walk {S I G : Type*} [Add G] (step : S → I → S × G) (v : S × G) :
    List I → S × G
  | [] => v
  | d :: ds =>
    let next := step v.1 d
    walk step (next.1, v.2 + next.2) ds

end ThresholdFrontier

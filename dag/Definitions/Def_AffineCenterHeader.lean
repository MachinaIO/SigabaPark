import Mathlib

namespace AffineCenterHeader

/-- Translate one side of an edge-respecting partition. -/
def cutShift {V W : Type} [AddCommGroup W] (side : V → Bool) (P : V → W)
    (a : W) (v : V) : W := if side v then P v + a else P v

/-- Delta for an ordered public edge, negated when the path traverses it backwards. -/
def edge {V W : Type} [AddCommGroup W] (P : V → W) (u v : V) : W := P v - P u

/-- Sum the oriented edges of a supplied walk. -/
def walkSum {V W : Type} [AddCommGroup W] (P : V → W) (u : V) : List V → W
  | [] => 0
  | v :: vs => edge P u v + walkSum P v vs

end AffineCenterHeader

import Definitions.Def_AffineCenterHeader

open AffineCenterHeader

set_option exponentiation.threshold 1024

theorem solution {V W : Type} [AddCommGroup W] (P : V → W) (u : V) (vs : List V) :
    walkSum P u vs = P (vs.getLastD u) - P u := by
  induction vs generalizing u with
  | nil => simp [walkSum]
  | cons v vs ih =>
    rw [walkSum, ih]
    cases vs <;> simp [edge, List.getLastD]

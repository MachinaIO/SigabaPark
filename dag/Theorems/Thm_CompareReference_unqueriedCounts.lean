import Definitions.Def_CompareReference

theorem CompareReference.unqueriedCounts {X : Type*} [Fintype X] [DecidableEq X] (x : X) (p : CompareReference.Probe X) :
    Nat.card {f : X → Bool // CompareReference.event x p true f} =
    Nat.card {f : X → Bool // CompareReference.event x p false f} := by
  sorry

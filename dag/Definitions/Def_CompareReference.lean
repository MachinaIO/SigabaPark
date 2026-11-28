import Mathlib.SetTheory.Cardinal.Finite

namespace CompareReference

inductive Probe (X : Type*) where
  | leaf (result : Bool)
  | ask (index : X) (next : Bool → Probe X)

def transcript {X : Type*} (f : X → Bool) : Probe X → List X × Bool
  | .leaf b => ([], b)
  | .ask i next =>
    let t := transcript f (next (f i))
    (i :: t.1, t.2)

def flip {X : Type*} [DecidableEq X] (x : X) (f : X → Bool) (i : X) : Bool :=
  if i = x then !(f i) else f i

def event {X : Type*} (x : X) (p : Probe X) (hit : Bool) (f : X → Bool) : Prop :=
  x ∉ (transcript f p).1 ∧ ((transcript f p).2 == f x) = hit

end CompareReference

import Mathlib

namespace ProjectiveJoin

noncomputable def bad {F : Type} [Field F] [DecidableEq F]
    (d : Nat) (p : Polynomial F) : Finset (Option F) :=
  let finite := p.roots.toFinset.map ⟨some, Option.some_injective F⟩
  if p.natDegree<d then insert none finite else finite

def atPoint {F : Type} [Field F] (d : Nat) (p : Polynomial F) : Option F → F
  | none => p.coeff d
  | some x => p.eval x


def dot3 (a b : Fin 8) : Bool :=
  Bool.xor (a.val.testBit 0 && b.val.testBit 0)
    (Bool.xor (a.val.testBit 1 && b.val.testBit 1) (a.val.testBit 2 && b.val.testBit 2))


def omitted (i : Fin 7) : Nat := [13,14,21,23,25,28,29][i.val]!


end ProjectiveJoin

import Mathlib.Tactic
import SigabaNeoStd.Machines.Gates

namespace AdvancedEncryption.WE.DensityTrials

/-- A complete Boolean evaluation table in variable-splitting order. -/
inductive Table : Nat → Type where
  | leaf (b : Bool) : Table 0
  | fork {n : Nat} (a b : Table n) : Table (n+1)
deriving DecidableEq

def weight {n : Nat} : Table n → Nat
  | .leaf b => if b then 1 else 0
  | .fork a b => weight a + weight b

def delta {n : Nat} : Table n → Table n → Table n
  | .leaf a, .leaf b => .leaf (xor a b)
  | .fork a b, .fork c d => .fork (delta a c) (delta b d)

/-- Multilinear degree at most d, recursively via f(x,t) = a(x) + t(a(x)+b(x)). -/
def Low : {n : Nat} → (d : Nat) → Table n → Prop
  | _, _, .leaf _ => True
  | _, 0, .fork a b => a = b ∧ Low 0 a
  | _, d+1, .fork a b => Low (d+1) a ∧ Low d (delta a b)

/-- NAND step on one Boolean column per wire, with componentwise operations and a true column
for every unavailable address. -/
def batchStep {I : Type} (s : List (I → Bool) × (I → Bool)) (g : Nat × Nat) :
    List (I → Bool) × (I → Bool) :=
  let v := fun i => !((s.1.getD g.1 (fun _ => true)) i && (s.1.getD g.2 (fun _ => true)) i)
  (s.1 ++ [v], v)

end AdvancedEncryption.WE.DensityTrials

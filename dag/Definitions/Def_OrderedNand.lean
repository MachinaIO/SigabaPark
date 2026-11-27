import Mathlib
import SigabaNeoStd.Machines.Gates

namespace OrderedNand
inductive Key where
  | dummy
  | wire (index : Nat) (bit : Bool)
  deriving DecidableEq

def live (v : Nat → Bool) : Key → Prop
  | .dummy => True
  | .wire i b => v i = b

def allowed (i : Nat) (b : Bool) : Prop := i = 0 → b = true

/-- l,r are already sorted after replacing both forward references by zero. -/
def row (d l r : Nat) (p q y : Key) : Prop :=
  if l = r then ∃ b, allowed l b ∧ p = .dummy ∧ q = .wire l b ∧ y = .wire d (!b)
  else ∃ a b, allowed l a ∧ allowed r b ∧ p = .wire l a ∧ q = .wire r b ∧
    y = .wire d (!(a && b))

def norm (size idx : Nat) := if idx < size then idx else 0

abbrev Tags (I : Type) := Set (I × Bool)
def extendsT {I : Type} (x : I → Bool) (S : Tags I) :=
  ∀ i b, (i,b) ∈ S → x i = b
def consistent {I : Type} (S : Tags I) := ∀ i, ¬ ((i,false) ∈ S ∧ (i,true) ∈ S)

/-- Project the successful sensitive-key records of a chronological log. -/
inductive Derives {I W : Type} (base : W → Tags I → Prop) (edges : W → W → W → Prop) :
    W → Tags I → Prop where
  | initial {w S} (h : base w S) : Derives base edges w S
  | gate {a b c A B} (p : Derives base edges a A) (q : Derives base edges b B)
      (r : edges a b c) : Derives base edges c (A ∪ B)
  | extra {w A B} (p : Derives base edges w A) (h : A ⊆ B) : Derives base edges w B
open SigabaNeo
def physical (n : Nat) (g : Nat × Nat) : Nat × Nat :=
  (min (norm n g.1) (norm n g.2), max (norm n g.1) (norm n g.2))
def compiled (n : Nat) : GateList → GateList
  | [] => []
  | g::gs => physical n g :: compiled (n+1) gs
def val (xs : List Bool) (i : Nat) := xs.getD i true
open SigabaNeo
def issued (n : Nat) : GateList → Key → Key → Key → Prop
  | [], _, _, _ => False
  | g::gs, p,q,y =>
    row n (physical n g).1 (physical n g).2 p q y ∨ issued (n+1) gs p q y
inductive Inputs (n : Nat) : Key → Tags (Fin n) → Prop where
 | dummy : Inputs n .dummy ∅
 | const : Inputs n (.wire 0 true) ∅
 | lit (i : Fin n) (b : Bool) : Inputs n (.wire (i.val+1) b) {(i,b)}
end OrderedNand

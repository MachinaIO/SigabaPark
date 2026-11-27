import Mathlib
namespace SemSep
def nand (a b : Bool) := !(a && b)
def shape {A : Type} (old new : A→A) : List A→List A
| [] => []
| v::vs => old v::vs.map new

/-- Process an actual row of broadcasts: the immediately following column is skipped. -/
inductive Expanded {A : Type} (op : A→A→A) : List A→List A→Prop where
| nil : Expanded op [] []
| cons (u : A) (xs ys : List A) (rest : Expanded op (shape id (op u) xs) ys) :
    Expanded op (u::xs) (u::ys)

def scan {A : Type} (op : A→A→A) (old new : A→A) : List A→List A
| [] => []
| v::vs => old v :: scan op new ((op (old v)) ∘ new) vs

def applyRows : List Bool→Bool→Bool
| [],x => x
| b::bs,x => applyRows bs (nand b x)
def flipN : Nat→Bool→Bool
| 0,x => x
| n+1,x => flipN n (!x)

def accept {S X : Type} (T : S→X→S) (ok : S→Bool) (s : S) (word : List X) :=
  ok (word.foldl T s)

def step (s : Nat×Nat×Nat) (x : Bool) (first : Bool) : Nat×Nat×Nat :=
  let y:=((s.1 / (2^x.toNat))%2==1)
  (s.2.1,(if y then 3-s.2.1 else 3),(if first then y else nand (s.2.2==1) y).toNat)
def shapes : Nat→List (Nat×Nat×Nat)
| 0 => [(2,2,0)]
| i+1 => ((shapes i).flatMap (fun s => [step s false (i==0),step s true (i==0)])).eraseDups

def evenStates : List (Nat×Nat×Nat) := [(1,2,0),(1,3,1),(0,3,1),(3,0,0),(3,3,1)]
def oddStates : List (Nat×Nat×Nat) := [(2,1,1),(2,3,1),(0,3,1),(3,0,0),(3,3,1)]
end SemSep

import Definitions.Def_VariableTagFront
import SigabaNeoStd.Machines.Gates
import Mathlib.Tactic
namespace VariableLocalReplay
open VariableTagFront

/-- Control-state handoff between the two zero-offset native scalar lookups and the append. -/
def nativeNand (a b : Bool) : Bool :=
  let mode := (step 77000 none none (some a) none).q - 75001
  let emit := (step (77000+mode) none none (some b) none).q
  ((step emit none none none none).ws.join).getD false

def replay (xs : List Bool) : List (Nat × Nat) → Option (List Bool)
  | [] => some xs
  | (a,b)::gs => do
    let u ← xs[a]?
    let v ← xs[b]?
    replay (xs ++ [nativeNand u v]) gs

/-- A missing/future local gate is rejected; an arbitrary length is supported. -/
def Backward (n : Nat) : List (Nat × Nat) → Prop
  | [] => True
  | (a,b)::gs => a<n ∧ b<n ∧ Backward (n+1) gs

def hit (k : Nat) (b : Bool) : A :=
  if k=0 then {q:=75001+256*(1+b.toNat)} else {q:=78000+(!(k==2 && b)).toNat}

def scan (x r t : Option Bool) : Nat → Nat → List Bool → A
  | 0,q,xs => step q x r xs.head? t
  | n+1,q,xs =>
    let a := step q x r xs.head? t
    if a.ms = 1 then scan x r t n a.q xs.tail else a

def activeGate (xs : List Bool) (p : Nat × Nat) : Option Bool := do
  let a := scan none none none p.1 (77000+p.1) xs
  if a.q=bad then none else
    let k := (a.q-75001)/256
    let b := scan none none none p.2 (77000+256*k+p.2) xs
    if b.q=bad then none else (step b.q none none none none).ws.join

def activeProgram (xs : List Bool) : List (Nat × Nat) → Option (List Bool)
  | [] => some xs
  | p::gs => do
    let b ← activeGate xs p
    activeProgram (xs++[b]) gs

def Bytes (gs : List (Nat × Nat)) := ∀ g ∈ gs, g.1<256 ∧ g.2<256

end VariableLocalReplay

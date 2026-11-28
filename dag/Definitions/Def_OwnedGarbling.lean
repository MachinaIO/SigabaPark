import Mathlib

namespace OwnedGarbling

structure Wire where
  ref : Option Nat
  tab : Bool → Bool

structure Gate where
  out : Nat
  left : Nat
  right : Nat

def joint (a b : Option Nat) : Bool :=
  match a, b with
  | some i, some j => decide (i ≠ j)
  | _, _ => false

def shape (k : Nat) (a b : Option Nat) : Option Nat :=
  if joint a b then some k else a.orElse (fun _ ↦ b)

def atBit (w : Wire) (b : Bool) := w.tab (if w.ref.isSome then b else false)

def combine (k : Nat) (x y : Wire) : Wire :=
  ⟨shape k x.ref y.ref, if joint x.ref y.ref then id
   else fun b ↦ !(atBit x b && atBit y b)⟩

def value (env : Nat → Bool) (w : Wire) := w.tab (w.ref.elim false env)

def emit (st : Nat → Wire) (g : Gate) : Nat → Wire :=
  Function.update st g.out (combine g.out (st g.left) (st g.right))

def publicStep (st : Nat → Option Nat) (g : Gate) : Nat → Option Nat :=
  Function.update st g.out (shape g.out (st g.left) (st g.right))

abbrev Tape (P C I : Type) := (P → ZMod 2) × (C → I → ZMod 2) × (C → ZMod 2)

/-- Exact change of independent setup variables into the random fields visible
in all keys and rows of the bounded sparse affine scheme. -/
def affineCoins {P C I : Type} [Fintype I] (who : C → I → P)
    (theta : P → ZMod 2) (a : C → I → ZMod 2) : Tape P C I ≃ Tape P C I where
  toFun v := (fun p ↦ theta p + v.1 p, fun c i ↦ a c i + v.2.1 c i,
    fun c ↦ v.2.2 c + ∑ i, theta (who c i) * v.2.1 c i)
  invFun v := (fun p ↦ v.1 p - theta p, fun c i ↦ v.2.1 c i - a c i,
    fun c ↦ v.2.2 c - ∑ i, theta (who c i) * (v.2.1 c i - a c i))
  left_inv := by intro v; simp
  right_inv := by intro v; simp

end OwnedGarbling

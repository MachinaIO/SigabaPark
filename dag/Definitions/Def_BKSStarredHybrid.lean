import Mathlib

namespace BKSStarredHybrid

/-- Encoded fields, tapes, and outputs of algorithms on classical strings. -/
abbrev Word := Nat

/-- A suffix row carries its child slot and its index within that slot. -/
abbrev Row {r : Nat} (n : Fin r → Nat) := (s : Fin r) × Fin (n s)

inductive ChildMessage where
  | pair (first second : Word)
  | single (value : Word)
  deriving DecidableEq

/-- The master/PRF-key pair in a live first row; none encodes the two dummies. -/
abbrev Secrets := Option (Word × Word)

structure Tables (a r q : Nat) (n : Fin r → Nat) where
  first : Bool → Fin a → Word
  tail : Bool → Row n → Word
  func : Bool → Fin q → Word

/-- The caller supplies independent local and child sources. Each contains all
the coins needed by that source, so repeated frame fields refer to the same draw. -/
structure Local (a r q : Nat) (n : Fin r → Nat) where
  outer : Word
  inner : Word
  live : Fin a → Word × Word
  rowTag : Fin a → Word
  outerRand : Fin a → Word
  aggRand : Fin a → Word
  tau : Row n → Word
  tailRand : Row n → Word
  z : Fin q → Word
  keyRand : Fin q → Word
  context : Word

structure Star (r q : Nat) (n : Fin r → Nat) where
  master : Word
  encRand : Row n → Word
  kgRand : Fin q → Word

/-- Algorithm interfaces, with separate slot and circuit encodings. -/
structure Ops where
  childE : Word → Nat → ChildMessage → Word → Word
  childKG : Word → Word → Word → Word
  packC : Word → Word
  outerE : Word → Secrets → Bool → Word → Word
  aggKG : Word → Word → Word → Bool → Word → Secrets → Word → Word
  tailE : Word → Nat → Word → Word → Word → Word → Word → Word → Word
  issuerKG : Word → Word → Word → Word → Word → Word → Word

structure View (a r q : Nat) (n : Fin r → Nat) where
  first : Fin a → Word × Word
  tail : Row n → Word
  keys : Fin q → Word
  context : Word

variable {a r q : Nat} {n : Fin r → Nat}

def childPlain (t : Tables a r q n) (j : Fin a) (d : Bool) (u : Row n) : ChildMessage :=
  if u.1.val = 0 then .pair (t.first d j) (t.tail d u) else .single (t.tail d u)

/-- Observable pair in each first-coordinate row in H(6,j) and H(7,j).
The distinguished row suppresses its real master in both fields. -/
def firstFrame (op : Ops) (t : Tables a r q n) (o : Local a r q n)
    (b : Bool) (j i : Fin a) : Word × Word :=
  let caps := if i = j then none else some (o.live i)
  let flag := decide (i.val < j.val)
  (op.outerE o.outer caps flag (o.outerRand i),
   op.aggKG o.inner (t.first b i) (t.first true i) flag (o.rowTag i) caps (o.aggRand i))

/-- Directly sample the hybrid: all embedded FE fields use the same child
master; ordinary fields always use the external bit b. -/
def honestFrame (op : Ops) (t : Tables a r q n) (b e : Bool) (j : Fin a)
    (o : Local a r q n) (c : Star r q n) : View a r q n where
  first := firstFrame op t o b j
  tail := fun u ↦
    let d := if e then true else b
    let g := op.childE c.master u.1.val (childPlain t j d u) (c.encRand u)
    op.tailE o.inner u.1.val (t.tail b u) (t.tail true u) (o.tau u) (o.rowTag j) g (o.tailRand u)
  keys := fun k ↦
    let d := if e then true else b
    let v := op.childKG c.master (op.packC (t.func d k)) (c.kgRand k)
    op.issuerKG o.outer (t.func b k) (t.func true k) (o.z k) v (o.keyRand k)
  context := o.context

def selectPair {α : Type} (e : Bool) (p : α × α) := if e then p.2 else p.1

/-- These queries are computed before the challenger samples its master. -/
def commit (t : Tables a r q n) (j : Fin a) (b : Bool) (u : Row n) :=
  (childPlain t j b u, childPlain t j true u)

def keyPair (op : Ops) (t : Tables a r q n) (b : Bool) (k : Fin q) :=
  (op.packC (t.func b k), op.packC (t.func true k))

structure Answers (r q : Nat) (n : Fin r → Nat) where
  gamma : Row n → Word
  delta : Fin q → Word

/-- The challenger has one shared master for all list and KG responses. -/
def challenge (op : Ops) (t : Tables a r q n) (j : Fin a) (b e : Bool)
    (c : Star r q n) : Answers r q n where
  gamma := fun u ↦ op.childE c.master u.1.val (selectPair e (commit t j b u)) (c.encRand u)
  delta := fun k ↦ op.childKG c.master (selectPair e (keyPair op t b k)) (c.kgRand k)

/-- The simulator only has oracle replies. In particular it has neither a
starred master nor the child tapes. -/
def assemble (op : Ops) (t : Tables a r q n) (b : Bool) (j : Fin a)
    (o : Local a r q n) (rep : Answers r q n) : View a r q n where
  first := firstFrame op t o b j
  tail := fun u ↦ op.tailE o.inner u.1.val (t.tail b u) (t.tail true u) (o.tau u)
    (o.rowTag j) (rep.gamma u) (o.tailRand u)
  keys := fun k ↦ op.issuerKG o.outer (t.func b k) (t.func true k) (o.z k)
    (rep.delta k) (o.keyRand k)
  context := o.context

/-- A private aggregator either routes the precomputed overrides or evaluates its
own row-indexed fallback table. The suffix has at least one slot in the reduction. -/
noncomputable def route {I S X W : Type} (k : I) (table : S → X → W)
    (inputs : S → X × Option I × W) : S → W := by
  classical
  exact if ∀ s, (inputs s).2.1 = some k then fun s ↦ (inputs s).2.2
    else fun s ↦ table s (inputs s).1

end BKSStarredHybrid

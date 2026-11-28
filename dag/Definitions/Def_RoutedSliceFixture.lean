import Mathlib.Tactic
namespace RoutedSliceFixture

/-- Each wire records its native NAND value and its value on the selected route. -/
abbrev Wire := Bool × Bool
def pin (b : Bool) : Wire := (b,b)
def gate (a b : Wire) (right : Bool) : Wire × Nat :=
  let chosen := if right then b.2 else a.2
  let other := if right then a.2 else b.2
  ((!(a.1 && b.1),!chosen),if chosen && !other then 1 else 0)
def zero := (gate (pin true) (pin true) false).1
def test (x s : Bool) : Wire × Nat :=
  let g := gate (pin x) zero (!s)
  let k := gate zero g.1 false
  (k.1,g.2+k.2)
theorem test_spec (x s : Bool) : test x s=(pin true,if x && s then 1 else 0) := by
  cases x <;> cases s <;> decide

def andWire (x y : Wire) : Wire × Nat :=
  let n := gate x y false
  let k := gate n.1 n.1 false
  (k.1,n.2+k.2)
theorem and_one : andWire (pin true) (pin true)=(pin true,0) := by decide
def tests (pairs : List (Bool × Bool)) := pairs.map fun p ↦ test p.1 p.2
def energy (pairs : List (Bool × Bool)) :=
  (pairs.map fun p ↦ if p.1 && p.2 then 1 else 0).sum
def reduce : List (Wire × Nat) → Wire × Nat
  | [] => (pin true,0)
  | [x] => x
  | x::y::ys =>
    let z := reduce (y::ys)
    let w := andWire x.1 z.1
    (w.1,x.2+z.2+w.2)
def pad (result : Wire × Nat) : Nat → Wire × Nat
  | 0 => result
  | n+1 =>
    let s := pad result n
    let b := andWire s.1 s.1
    (b.1,s.2+b.2)
theorem joins (pairs : List (Bool × Bool)) : reduce (tests pairs)=(pin true,energy pairs) := by
  induction pairs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => simp [tests,reduce,test_spec,energy]
    | cons y ys =>
      change (let z := reduce (tests (y::ys)); let w := andWire (test x.1 x.2).1 z.1;
        (w.1,(test x.1 x.2).2+z.2+w.2))=_
      simp [ih,test_spec,and_one,energy]
theorem pads (n e : Nat) : pad (pin true,e) n=(pin true,e) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pad,ih,and_one]

def terminal (yes : Bool) (v : Wire) := gate v (if yes then zero else v) yes
def run (yes : Bool) (pairs : List (Bool × Bool)) (p : Nat) : Bool × Nat :=
  let s := pad (reduce (tests pairs)) p
  let t := terminal yes s.1
  (t.1.1,s.2+t.2+(if t.1.2 then 0 else 1))
theorem run_spec (yes : Bool) (pairs : List (Bool × Bool)) (p : Nat) :
    run yes pairs p=(yes,energy pairs+(if yes then 0 else 1)) := by
  unfold run
  rw [joins,pads]
  cases yes <;> rfl

/-- One zero, two gates per input, 127 pairs for the conjunction,
1792 two-gate padding pairs and the final output gate. -/
theorem count : 1+2*128+2*127+2*1792+1=4096 := by decide

/-- Representatives with j coincident one bits followed by zeros. -/
def rep (j : Fin 129) := List.replicate j.val (true,true)++List.replicate (128-j.val) (false,false)
theorem replays (j : Fin 129) :
    (rep j).length=128 ∧ energy (rep j)=j.val := by
  constructor
  · simp [rep]; omega
  · simp [energy,rep,List.sum_append]
end RoutedSliceFixture

import Definitions.Def_SeparatingTerminalMachine
import SigabaNeo.Trusted.Primitive
import Mathlib

namespace StaticRelease182
open SigabaNeo Turing SeparatingTerminalMachine

/-- Directions: 0 stay, 1 right, 2 left. Work bits are initialized blank. -/
structure A where
  q : Option Nat := none
  mi : Nat := 0
  m0 : Nat := 0
  m1 : Nat := 0
  m2 : Nat := 0
  w0 : Option Bool := none
  w1 : Option Bool := none
  w2 : Option Bool := none
  out : Option Bool := none
deriving Inhabited

def sign (x : Nat) : SignType := if x=1 then 1 else if x=2 then -1 else 0
def put (r k : Nat) (b : Bool) : Nat := if r.testBit k == b then r else r ^^^ (2^k)
def base (n : Nat) := 2+63*(n+1)
def encStates (n : Nat) := base n+23*3*16
def ec (n ph role r : Nat) := base n+(ph*3+role)*16+r
def equivBit (t i : Nat) : Bool :=
  allow (finProdFinEquiv.symm (Fin.ofNat 63 t)) (2,Fin.ofNat 4224 i)

def en (n : Nat) (eq : Nat → Nat → Bool) (q : Nat) (input rom flags : Option Bool) (coin : Bool) : A := Id.run do
  if q<2 then return {q := some (q+1), m0 := 1}
  if q<base n then
    let j := q-2
    return {q := some (q+1), m0 := 1, w0 := if j%(n+1)<n then some (eq (j/(n+1)) (j%(n+1))) else none}
  let p := q-base n
  let ph := p/48
  let ro := p/16%3
  let r := p%16
  let go := fun h a b => some (ec n h a b)
  let w := fun h => go h ro r
  let b := r.testBit 0
  let u := r.testBit 1
  let v := r.testBit 2
  let pad := r.testBit 3
  let eligible := if ro=2 then rom.getD false else !(rom.getD false)
  let share := if ro=0 then u else if ro=1 then v else (b ^^ u) ^^ v
  match ph with
  | 0 => return {q := w 1,m0 := 2}
  | 1 => return {q := w 2,m0 := 2}
  | 2 => return {q := w (if rom.isSome then 2 else 3),m0 := 2}
  | 3 => return {q := w (if rom.isSome then 2 else 4),m0 := if rom.isSome then 2 else 1}
  | 4 => return {q := w 5,m0 := 1,m1 := 1}
  | 5 => match input with
    | none => return {}
    | some f => return {q := w (if f then 6 else 10),mi := 1}
  | 6 => return {q := w 5,mi := 1}
  | 7 => if input=some true then return {q := w 8,mi := 1} else return {}
  | 8 => match input with
    | none => return {}
    | some f => return {q := go 9 ro (put r 0 f),mi := 1}
  | 9 => if input=some false then return {q := w 12,mi := 1} else return {}
  | 10 => match input with
    | none => return {}
    | some true => return {q := w 11,mi := 1,out := some true}
    | some false => return {q := w 7,mi := 1,m1 := 2}
  | 11 => match input with
    | none => return {}
    | some f => return {q := w 10,mi := 1,m1 := 1,w1 := some f,out := some f}
  | 12 => return {q := w (if flags.isSome then 12 else 13),m1 := if flags.isSome then 2 else 1}
  | 13 => return {q := go 14 0 (put r 1 coin)}
  | 14 => return {q := go 15 0 (put r 2 coin)}
  | 15 =>
    if rom.isNone then
      if ro<2 then return {q := go 21 (ro+1) r,m0 := 2}
      if flags.isSome then return {}
      return {q := go 22 0 r,m0 := 1}
    if flags.isNone then return {}
    return {q := go 16 ro (put r 3 coin),w2 := some coin,m2 := 1,out := some true}
  | 16 => return {q := w 17,out := some (eligible && flags.getD false)}
  | 17 => return {q := w 18,out := some true}
  | 18 => return {q := w 19,out := some (eligible && (pad ^^ share))}
  | 19 => return {q := w 20,out := some true}
  | 20 => return {q := w 15,m0 := 1,m1 := 1,out := some (flags.getD false && pad)}
  | 21 => return {q := w (if rom.isSome then 21 else 15),m0 := if rom.isSome then 2 else 1}
  | 22 => if rom.isNone then return {out := some false} else return {q := w 12,m1 := 2}
  | _ => return {}

def encMachine : Machine where
  tapes := 3
  states := encStates 4224
  time := 2^24
  machine := {
    initial := ⟨0,by decide⟩
    tr := fun q i w _ coin =>
      let a := en 4224 equivBit q.val i (w 0) (w 1) coin
      let nxt := a.q.bind fun c => if h : c < encStates 4224 then some ⟨c,h⟩ else none
      .step { inputTape := sign a.mi
              workTapes := fun t =>
                let x := if t.val=0 then a.w0 else if t.val=1 then a.w1 else a.w2
                (x.map some, sign (if t.val=0 then a.m0 else if t.val=1 then a.m1 else a.m2))
              output := a.out
              state := nxt } (fun x => Fin.elim0 x) (fun x => Fin.elim0 x) }

def deBase (n : Nat) := 6+6*n
def tailBase (n : Nat) := deBase n+3*n*6*16
def decStates (n : Nat) := tailBase n+3
def dc (n role i ph r : Nat) := deBase n+((role*n+i)*6+ph)*16+r
def de (n q : Nat) (input : Option Bool) : A := Id.run do
  if q<6 then
    if q%2=1 then return {q := some (q-1),mi := 1}
    let some f := input | return {}
    return {q := some (if f then q+1 else q+2),mi := 1}
  if q<deBase n then
    if (q-6)%2=0 && input != some true then return {}
    if input.isNone then return {}
    return {q := some (if q+1=deBase n then dc n 0 0 0 2 else q+1),mi := 1}
  if q≥tailBase n then
    if q=tailBase n+2 then return {out := some false}
    return {q := some (tailBase n+2),out := some (q=tailBase n+1)}
  let s := q-deBase n
  let r := s%16
  let ph := s/16%6
  let i := s/(16*6)%n
  let ro := s/(16*6*n)
  let go := fun h a => some (dc n ro i h a)
  let already := r.testBit 0
  let prev := r.testBit 1
  let par := r.testBit 2
  let want := r.testBit 3
  let some f := input | return {}
  if ph%2=0 then
    if f then return {q := go (ph+1) r,mi := 1}
    if ph=0 then return {q := some (tailBase n),out := some true} else return {}
  if ph=1 then return {q := go 2 (put r 3 (f && !already)),mi := 1}
  if ph=3 then return {q := go 4 (put r 2 (par ^^ (f && want))),mi := 1}
  let val := par ^^ (f && want)
  let found := already || want
  let next := if i+1<n then dc n ro (i+1) 0 (put (put (put r 2 val) 0 found) 3 false)
              else if ro<2 then dc n (ro+1) 0 0 (put (put 0 1 (prev && found)) 2 val)
              else dc n 0 0 0 2
  if i+1=n && ro=2 && prev && found then
    return {q := some (tailBase n+val.toNat),out := some true,mi := 1}
  return {q := some next,mi := 1}

def decMachine : Machine where
  tapes := 0
  states := decStates 4224
  time := 2^23
  machine := {
    initial := ⟨0,by decide⟩
    tr := fun q i _ _ _ =>
      let a := de 4224 q.val i
      let nxt := a.q.bind fun c => if h : c < decStates 4224 then some ⟨c,h⟩ else none
      .step { inputTape := sign a.mi, workTapes := fun t => Fin.elim0 t,
              output := a.out, state := nxt }
            (fun x => Fin.elim0 x) (fun x => Fin.elim0 x) }

theorem full_static_local_budget :
    encMachine.cost + decMachine.cost < 2^31 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- The actual three data-emission states agree with the dense correction and authorized-pad semantics. -/
theorem slot_emissions :
    ∀ (ro : Fin 3) (r : Fin 16) (eqr flag : Bool),
    let bit := fun (ph : Nat) =>
      (en 4224 equivBit (ec 4224 ph ro r) none (some eqr) (some flag) false).out
    let eligible := if ro.val=2 then eqr else !eqr
    let share := AdvancedEncryption.WE.SeparatingTerminal.roleShare
      (r.val.testBit 0) (r.val.testBit 1) (r.val.testBit 2) ro
    bit 16 = some (eligible && flag) ∧
    bit 18 = some (eligible && ((r.val.testBit 3) ^^ share)) ∧
    bit 20 = some (flag && r.val.testBit 3) := by decide

/-- The raw static packet and its single-field machine output lengths. -/
theorem lengths :
    2*63 + 3*4224*63 = 798462 ∧
    3*4224 + 3*(3*4224*63) = 2407680 ∧
    2*2407680+1 = 4815361 := by decide

end StaticRelease182

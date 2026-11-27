import Mathlib
import SigabaNeo.Trusted.Machine
import SigabaNeoStd.Machines.Gates
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

namespace FrontierNandCompiler

open SigabaNeo Turing Turing.MultiTapeTM

def decodeWirePairs (s : List Bool) : GateList :=
  (frames s).map fun g => ((unframe g).length,(dropFrame g).length)

/-- One action: numeric next phase, next count, move right?, optional output.
    Missing successor halts. Phases 32..44 and 45..57 emit little-endian operands. -/
def parseAction (ph n : Nat) (bit : Option Bool) :
    Option (Nat × Nat × Bool × Option Bool) := Id.run do
  if 32 ≤ ph ∧ ph < 58 then
    let k := (ph-32)%13
    let next := if k=12 then (if ph<45 then 18 else 10) else ph+1
    return some (next, if k=12 then 0 else n, false, some (n.testBit k))
  let some b := bit | return none
  if ph=0 then return some (if b then 1 else 10,0,true,none)
  if ph=1 then return some (0,0,true,none)
  if ph<10 ∨ ph>21 then return none
  if ph%2=0 then
    if b then return some (ph+1,n,true,none) else return none
  let c := (ph-11)/2
  match c with
  | 0 => if b then return some (12,n,true,none) else return none
  | 1 => return some (if b then 14 else 32,n,true,none)
  | 2 => if b then return some (16,n,true,none) else return none
  | 3 => if b && n<4224 then return some (10,n+1,true,none) else return none
  | 4 => return some (if b then 20 else 45,n,true,none)
  | _ => if b && n<4224 then return some (18,n+1,true,none) else return none

/-- A closed, zero-work-tape first stage on the registry's outer tuple.
    It consumes the parameter field, then the unary-pair circuit field, and writes raw 13-bit indices. -/
def parserMachine : SigabaNeo.Machine where
  tapes := 0
  states := 58*8192
  time := 2^28
  machine := {
    initial := 0
    tr := fun st bit _ _ _ =>
      let act := parseAction (st.val/8192) (st.val%8192) bit
      let next : Option (Fin (58*8192)) := act.bind fun (ph,n,_,_) =>
        if h : ph*8192+n < 58*8192 then some ⟨ph*8192+n,h⟩ else none
      .step {inputTape := if act.any (fun a => a.2.2.1) then 1 else 0
             workTapes := fun i => Fin.elim0 i
             output := act.bind fun a => a.2.2.2
             state := next} (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) }

/-- One fused carry: multiply an activity bit by a single mask and XOR it into an accumulated bit. -/
def fuse (b r v : Bool) : Bool := b ^^ (r && v)

end FrontierNandCompiler

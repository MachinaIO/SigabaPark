import SigabaNeoStd.Machines.FromPolyTime
import Mathlib.Tactic.DeriveFintype

namespace AdvancedEncryption.WE.TraceEmitter

open Turing SigabaNeo

/-- Tape 0 holds the decoded statement. Tape 1 stores true, the witness and the gates
in evaluation order. Tape 2 marks history address zero and travels with tape 1. -/
inductive Phase where
  | init | params | paramsData | statement | statementData | witness | witnessData
  | rewindStatement | rewindWitness | first | firstTag | firstThird | firstFourth
  | homeSecond (a : Bool) | second (a : Bool) | secondPair (a : Bool)
  | homeAppend (v : Bool) | appendBit (v : Bool) | emitBit (v : Bool) | homeGate
  deriving DecidableEq, Fintype

abbrev Act := Action 3 Bool Phase

def action (q : Option Phase) (i s h : SignType)
    (statement history origin out : Option Bool := none) : Act where
  inputTape := i
  workTapes t :=
    if t = 0 then (statement.map some, s)
    else if t = 1 then (history.map some, h) else (origin.map some, h)
  output := out
  state := q

def tr (q : Phase) (i : Option Bool) (t : Fin 3 → Option Bool) : Act :=
  let s := t 0
  let h := t 1
  let atHome := (t 2).isSome
  let stop := action none 0 0 0
  match q with
  | .init => action (some .params) 0 0 1 none (some true) (some true)
  | .params =>
    match i with
    | some true => action (some .paramsData) 1 0 0
    | some false => action (some .statement) 1 0 0
    | none => stop
  | .paramsData => action (some .params) 1 0 0
  | .statement =>
    match i with
    | some true => action (some .statementData) 1 0 0
    | some false => action (some .witness) 1 0 0
    | none => stop
  | .statementData => action (some .statement) 1 1 0 i
  | .witness =>
    match i with
    | some true => action (some .witnessData) 1 0 0
    | some false => action (some .rewindStatement) 1 (-1) 0
    | none => stop
  | .witnessData => action (some .witness) 1 0 1 none i
  | .rewindStatement =>
    if s.isSome then action (some .rewindStatement) 0 (-1) 0
    else action (some .rewindWitness) 0 1 0
  | .rewindWitness =>
    if atHome then action (some .first) 0 0 0 else action (some .rewindWitness) 0 0 (-1)
  | .first =>
    match s with
    | none => action none 0 0 0 none none none (some false)
    | some true => action (some .firstTag) 0 1 0
    | some false => stop
  | .firstTag =>
    match s with
    | some true => action (some .firstThird) 0 1 0
    | some false => action (some (.homeSecond (h.getD true))) 0 1 0
    | none => stop
  | .firstThird => if s == some true then action (some .firstFourth) 0 1 0 else stop
  | .firstFourth => if s == some true then action (some .first) 0 1 1 else stop
  | .homeSecond a =>
    if atHome then action (some (.second a)) 0 0 0
    else action (some (.homeSecond a)) 0 0 (-1)
  | .second a =>
    match s with
    | some true => action (some (.secondPair a)) 0 1 0
    | some false => action (some (.homeAppend (!(a && h.getD true)))) 0 1 0
    | none => stop
  | .secondPair a => if s == some true then action (some (.second a)) 0 1 1 else stop
  | .homeAppend v =>
    if atHome then action (some (.appendBit v)) 0 0 0
    else action (some (.homeAppend v)) 0 0 (-1)
  | .appendBit v =>
    if h.isSome then action (some (.appendBit v)) 0 0 1
    else action (some (.emitBit v)) 0 0 0 none (some v) none (some true)
  | .emitBit v => action (some .homeGate) 0 0 0 none none none (some v)
  | .homeGate =>
    if atHome then action (some .first) 0 0 0 else action (some .homeGate) 0 0 (-1)

def tm : MultiTapeTM 3 Bool Phase := MultiTapeTM.ofTr .init tr

/-- Traversal accounting: frame tags, spool rewind, witness rewind, all source walks,
history length scans and framed trace writes. No ciphertext length term occurs. -/
def clock : ℕ := 2 * 515 + 3 * 103821312 + 3 * 128 + 9 + 4096 * (10 * 4224 + 8)

noncomputable def machine := Machine.ofTM tm clock

end AdvancedEncryption.WE.TraceEmitter

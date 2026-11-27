import Definitions.Def_WE_CircuitSAT
import SigabaNeoStd.Machines.FromPolyTime
import Mathlib.Tactic.DeriveFintype

namespace AdvancedEncryption.WE.UnaryTraceWalk

open Turing SigabaNeo

/-- Both work heads always move together. Tape zero contains the complete certificate;
tape one contains the constant, assignment and verified gate prefix. -/
inductive Phase where
  | start | turn | home | first | firstTag | firstThird | firstFourth
  | homeSecond (a : Bool) | second (a : Bool) | secondPair (a : Bool)
  | homeAppend (v : Bool) | appendBit (v : Bool) | advance (v : Bool)
  deriving DecidableEq, Fintype

abbrev State := Fin 4224 ⊕ Phase
abbrev Act := Action 2 Bool State

def act (q : Option State) (inputMove workMove : SignType)
    (certificate history emit : Option Bool := none) : Act where
  inputTape := inputMove
  workTapes t := ((if t = 0 then certificate else history).map some, workMove)
  output := emit
  state := q

def go (p : Phase) (i d : SignType) := act (some (.inr p)) i d

def finish (v : Bool) := act none 0 0 none none (some v)

def tr (q : State) (i : Option Bool) (w : Fin 2 → Option Bool) : Act :=
  let cert := w 0
  let hist := w 1
  match q with
  | .inl j =>
    match i with
    | none => finish false
    | some b =>
      let next : State := if h : j.val + 1 < 4224 then .inl ⟨j.val + 1, h⟩ else .inr .turn
      act (some next) 1 1 (some b) (if j.val < 128 then some b else none)
  | .inr .start => act (some (.inl 0)) 0 1 (some true) (some true)
  | .inr .turn => go .home 0 (-1)
  | .inr .home => if cert.isSome then go .home 0 (-1) else go .first 0 1
  | .inr .first =>
    if cert.isSome && i == some true then go .firstTag 1 0 else finish false
  | .inr .firstTag =>
    match i with
    | some true => go .firstThird 1 0
    | some false => go (.homeSecond (hist.getD true)) 1 (-1)
    | none => finish false
  | .inr .firstThird => if i == some true then go .firstFourth 1 0 else finish false
  | .inr .firstFourth => if i == some true then go .first 1 1 else finish false
  | .inr (.homeSecond a) =>
    if cert.isSome then go (.homeSecond a) 0 (-1) else go (.second a) 0 1
  | .inr (.second a) =>
    if cert.isSome then
      match i with
      | some true => go (.secondPair a) 1 0
      | some false => go (.homeAppend (!(a && hist.getD true))) 1 (-1)
      | none => finish false
    else finish false
  | .inr (.secondPair a) => if i == some true then go (.second a) 1 1 else finish false
  | .inr (.homeAppend v) =>
    if cert.isSome then go (.homeAppend v) 0 (-1) else go (.appendBit v) 0 1
  | .inr (.appendBit v) =>
    if hist.isSome then go (.appendBit v) 0 1
    else if cert == some v then act (some (.inr (.advance v))) 0 1 none (some v)
    else finish false
  | .inr (.advance v) =>
    if cert.isSome then go .home 0 (-1) else finish (v && i.isNone)

def tm : MultiTapeTM 2 Bool State := MultiTapeTM.ofTr (.inr .start) tr

/-- An upper envelope for the intended successful traversal, counted in head ticks. -/
def clock : ℕ := 8452 + 4096 * (10 * 4224 + 10)

noncomputable def machine := Machine.ofTM tm clock

/-- Private component interface: raw assignment and trace, followed by the registered statement. -/
def word (x : Fin 128 → Bool) (t : Fin 4096 → Bool) (φ : CircuitSAT.Circuit 128 4096) :=
  List.ofFn x ++ List.ofFn t ++ encGates φ.gates

/-- A reference trace contains every appended wire, including the final output. -/
def trace (x : List Bool) (gs : GateList) :=
  (gs.foldl estep (true :: x, true)).1.drop (x.length + 1)

end AdvancedEncryption.WE.UnaryTraceWalk

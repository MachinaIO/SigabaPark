import Definitions.Def_SerpentineRowMachine
namespace SerpentineBank
open SigabaNeo SerpentineRing
structure PlanAct extends Act where
  mv : SignType := 0
  wr : Option (Option Bool) := none

def cpBase (n : Nat) := 15+11*width n+4
def arBase (n : Nat) := cpBase n+7
def totalStates (n : Nat) := arBase n + states n

def front (n : Nat) (q : Nat) (inp a packet : Option Bool) (coin : Bool) : PlanAct := Id.run do
  let w:=width n
  let endq:=totalStates n
  if q<15 then
    let some b:=inp | return {q:=endq}
    let x:=2*q+1+b.toNat
    if x<15 then return {q:=x,im:=1}
    let op:=x-15
    let dest:=match op with
      | 0 => 15
      | 1 => 15+w
      | 2 => 15+2*w
      | 3 => 15+3*w
      | 4 => 15+4*w
      | 5 => 15+5*w+4
      | 6 => 15+5*w
      | 7 => 15+9*w+4
      | 8 => cpBase n+2
      | 9 => cpBase n
      | 10 => cpBase n+1
      | _ => endq
    return {q:=dest,im:=1,out:=if op==9 || op==10 then some true else none}
  if q<15+5*w then
    let i:=(q-15)%w
    let op:=(q-15)/w
    let go:=if i+1==w then 0 else q+1
    if op<=1 then return {q:=go,a:=1,aw:=some (some (if op==0 || i==3 then coin else false))}
    if op==2 then return {q:=go,a:= -1}
    if op==3 then return {q:=go,a:=1}
    let some v:=a | return {q:=endq}
    return {q:=go,a:=1,mv:=1,wr:=some (some v)}
  if q<15+5*w+4 then
    let i:=q-(15+5*w)
    let some v:=a | return {q:=endq}
    return {q:=if i==3 then 15+4*w+4 else q+1,a:=1,mv:=1,wr:=some (some (v ^^ (i==3)))}
  if q<15+9*w+4 then
    let z:=q-(15+5*w+4)
    let i:=z/4
    let b:=z%4
    let some v:=a | return {q:=endq}
    let next:=match i%4 with
      | 0 => v.toNat
      | 1 => b+2*v.toNat
      | 2 => b/2
      | _ => 0
    return { q:=if i+1==w then 0 else 15+5*w+4+4*(i+1)+next
             a:=1,mv:=1,wr:=some (some (i%4>=2 && b%2==1)) }
  if q<cpBase n then
    let i:=q-(15+9*w+4)
    let some v:=a | return {q:=endq}
    return {q:=if i+1==2*w then 0 else q+1,a:=if i%2==1 then 1 else 0,out:=some (i%2==0 || v)}
  let t:=q-cpBase n
  if t<2 then return {q:=0,out:=some (t==1)}
  if t==2 then return if a.isSome then {q:=q,a:=1} else {q:=q+1,a:= -1}
  if t==3 then return if a.isSome then {q:=q,a:= -1,aw:=some none} else {q:=q+1,a:=1}
  if t==4 then return {q:=q+1,mv:= -1}
  if t==5 then return if packet.isSome then {q:=q,mv:= -1} else {q:=q+1,mv:=1}
  return {q:=arBase n}

def joined (n q : Nat) (inp a k packet : Option Bool) (coin : Bool) : PlanAct :=
  if q<arBase n then front n q inp a packet coin else
  let v:=action n true (q-arBase n) packet a k coin
  {toAct:={v with q:=arBase n+v.q,im:=0},mv:=v.im}

def budget (n rows pool publ : Nat) := Id.run do
  let w:=width n
  return pool*(w+4) + 2*(2*w+4) + 2*rows*(w+4) + (2*rows+2)*pool*(w+4) +
    5*publ + 2*pool*w + 2*w*rows + 16 + rows*rowTime n+1

def machine (n rows pool publ : Nat) : Machine where
  tapes:=3
  states:=totalStates n
  time:=budget n rows pool publ
  machine:={
    initial:=⟨0, by simp [totalStates,arBase,cpBase,states]⟩
    tr:=fun q inp ws _ coin =>
      let v:=joined n q.val inp (ws 0) (ws 1) (ws 2) coin
      .step {
        inputTape:=v.im
        workTapes:=fun j => if j.val==0 then (v.aw,v.a) else if j.val==1 then (v.kw,v.k) else (v.wr,v.mv)
        output:=v.out
        state:=if h:v.q<totalStates n then some ⟨v.q,h⟩ else none
      } Fin.elim0 Fin.elim0}
end SerpentineBank

import SigabaNeoStd.Lattices.Algo.RingWords
import SigabaNeo.Trusted.Machine
namespace SerpentineRing
open SigabaNeo

def width (n : Nat) := 4*n
def dotBase (n : Nat) := 6*width n+4
def flushBase (n : Nat) := dotBase n+2*16*85
def tailBase (n : Nat) := flushBase n+3*16*12
def states (n : Nat) := tailBase n+2
def rowTime (n : Nat) := 8 * width n + 4 + n*(width n+13)
def offsetOf (p : Nat) := if p==0 then 0 else if p==1 then 1 else if p==2 then 5 else 21
def dot (n d acc p a b : Nat) := dotBase n+(d*16+acc)*85+offsetOf p+a*2^p+b
def flush (n d acc t : Nat) := flushBase n+(d*16+acc)*12+t
structure Act where
  q : Nat
  im : SignType := 0
  a : SignType := 0
  k : SignType := 0
  aw : Option (Option Bool) := none
  kw : Option (Option Bool) := none
  out : Option Bool := none

def action (n : Nat) (issue : Bool) (q : Nat) (inp a k : Option Bool) (coin : Bool) : Act := Id.run do
  let w := width n
  let stop : Act := {q:=states n}
  if q<2*w then
    let i:=q/2
    let seen:=q%2==1
    let some v:=inp | return {q:=states n,out:=if issue && q==0 then some false else none}
    let flag:=if i%4==3 then false else seen || v
    return {q:=if i+1==w then 2*w else 2*(i+1)+flag.toNat, im:=1,k:=1,kw:=some (some (v ^^ seen))}
  if q<3*w then return {q:=q+1,im:= -1}
  if q<4*w then
    let some v:=inp | return stop
    return {q:=q+1,im:=1,k:=1,kw:=some (some v)}
  if q<6*w then
    if (q-4*w)%2==0 then return {q:=q+1,out:=if issue then some true else none}
    let some v:=if issue then some coin else inp | return stop
    return {q:=q+1,im:=if issue then 0 else 1,a:=1,k:= -1,aw:=some (some v),out:=if issue then some v else none}
  if q<6*w+3 then return {q:=q+1,a:= -1,k:=1}
  if q==6*w+3 then
    return if a.isSome then {q:=q,a:= -1} else {q:=dot n 0 0 0 0 0,a:=1}
  if q<flushBase n then
    let localQ:=q-dotBase n
    let d:=localQ/(16*85)
    let acc:=localQ/85%16
    let code:=localQ%85
    let p:=if code<1 then 0 else if code<5 then 1 else if code<21 then 2 else 3
    let some x:=a | return if p==0 then {q:=flush n (if d==1 && k.isNone then 2 else d) acc 0} else stop
    let some y:=k | return stop
    let v:=code-offsetOf p
    let abits:=v/2^p
    let kbits:=v%2^p
    let aa:=if d==0 then abits+2^p*x.toNat else 2*abits+x.toNat
    let kk:=if d==0 then 2*kbits+y.toNat else kbits+2^p*y.toNat
    let dest:=if p==3 then dot n d ((acc+aa*kk)%16) 0 0 0 else dot n d acc (p+1) aa kk
    return {q:=dest,a:=if d==0 then 1 else -1,k:=if d==0 then -1 else 1}
  if q<tailBase n then
    let localQ:=q-flushBase n
    let d:=localQ/(16*12)
    let acc:=localQ/12%16
    let t:=localQ%12
    if issue && t<4 && inp.isNone then return stop
    let noise:=if !issue then 0 else if t==0 then coin.toNat else if t==1 then 15*coin.toNat else 0
    let add:=if issue && t<4 then 2^t*(inp.getD false).toNat else 0
    let v:=(acc+add+noise)%16
    let dst:=if t<11 then flush n d v (t+1) else if d==2 then tailBase n else dot n (1-d) 0 0 0 0
    let out:=if t<4 then none else if t%2==0 then (if issue then some true else none) else some (v.testBit ((t-4)/2))
    return {
      q := dst
      im := if issue && t<4 then 1 else 0
      a := if t != 0 then 0 else if d==0 then -1 else 1
      k := if (d==0 && t<5) || (d==1 && t<3) then 1 else 0
      out := out }
  if q==tailBase n then return {q:=q+1,k:= -1}
  return if k.isSome then {q:=q,k:= -1} else {q:=0,k:=1}

def machine (n rows : Nat) (issue : Bool) : Machine where
  tapes:=2
  states:=states n
  time:=rows*rowTime n+1
  machine:={
    initial:=⟨0,by simp [states]⟩
    tr:=fun q inp ws _ coin =>
      let v:=action n issue q.val inp (ws 0) (ws 1) coin
      .step {
        inputTape := v.im
        workTapes := fun j => if j.val==0 then (v.aw,v.a) else (v.kw,v.k)
        output := v.out
        state := if h:v.q<states n then some ⟨v.q,h⟩ else none
      } Fin.elim0 Fin.elim0}

end SerpentineRing
namespace SerpentineLaws
open SerpentineRing SigabaNeo.Lattices.Algo Cslib
def keyAt {R : Type*} [Neg R] (n : Nat) (key : Nat → R) (v : Nat) :=
  if v<n then -key v else key (v-n)
def pos (n j i bit : ℤ) := 4*(n+j-i)+3-bit
def neg4 (x : Nat) := (List.range 4).foldl (fun v i =>
  v + 2^i*(x.testBit i ^^ (x%2^i != 0)).toNat) 0
def runWord (dir x k carry : Nat) := (List.range 4).foldl (fun s t =>
  let abit := x.testBit (if dir==0 then t else 3-t)
  let kbit := k.testBit (if dir==0 then 3-t else t)
  (action 4 false s none (some abit) (some kbit) false).q) (dot 4 dir carry 0 0 0)
end SerpentineLaws
open SerpentineLaws SerpentineRing SigabaNeo.Lattices.Algo Cslib

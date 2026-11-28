import Definitions.Def_StreamBucketBank

namespace VariableTagFront
open SigabaNeo
structure A where
  q : Nat
  wr : Option (Option Bool) := none
  ws : Option (Option Bool) := none
  wt : Option (Option Bool) := none
  mr : SignType := 0
  ms : SignType := 0
  mt : SignType := 0
  mi : SignType := 0
  out : Option Bool := none

def bad := 150000
def left := 10000
def right := 45000
def word (side v : Nat) := 70000+512*side+256+v
def rev8 (v : Nat) := (List.range 8).foldl (fun a i=>a+if v.testBit i then 2^(7-i) else 0) 0

/-- Front-end subroutine. At q=120000 it has parsed 3200 raw local gates,
recorded the 256 flags in negative R cells, and emitted the framed first-role dictionary. -/
def step (q : Nat) (inp r s t : Option Bool) : A := Id.run do
  let fail : A := {q:=bad,out:=some false}
  if q≤1030 then
    let need:=q<1030 && (q%2==0 || (q/2<514 && (q/2)%257 != 256))
    if inp != some need then return fail
    if q==1030 then return {q:=1100,mi:=1,mr:= -1,ms:=1}
    return {q:=q+1,mi:=1}
  if 1100≤q && q<1356 then
    return {q:=q+1,wr:=some (some false),mr:=if q==1355 then 1 else -1}
  if q==1356 then
    if r.isSome then return {q:=q,mr:=1}
    return {q:=1400,mr:=1}
  if 1400≤q && q<4600 then return {q:=q+1,wr:=some (some false),mr:=1}
  if q==4600 then return {q:=4601,mr:= -1}
  if q==4601 then
    if r.isSome then return {q:=q,mr:= -1}
    return {q:=left,mr:=1}
  if (left≤q && q<left+33788) || (right≤q && q<right+16898) then
    let sd:=(if q≥right then 1 else 0)
    let n:=q-(if sd==0 then left else right)
    if inp.isNone then return fail
    if inp==some true then
      if n≥(if sd==0 then 33787 else 16897) then return fail
      return {q:=q+1,mi:=1}
    let scale:=if sd==0 then 8 else 4
    if n%scale != (if sd==0 then 3 else 1) then return fail
    let v:=n/scale
    if v==0 then return {q:=word sd 0,mi:=1}
    if v>3328 then return fail
    let role:=if v≤128 then (v-1)/8 else (v-129)/200
    let idx:=if v≤128 then 1+(v-1)%8 else 9+(v-129)%200
    return {q:=62500+209*(16*sd+role)+idx,mt:= -1,mi:=1}
  if 62500≤q && q<69188 then
    let z:=q-62500
    let rem:=z/209%16
    if t.isSome then
      if rem==0 then return fail
      return {q:=q-209,mt:= -1}
    if rem != 0 then return fail
    return {q:=69500+209*(z/3344)+z%209,mt:=1}
  if 69500≤q && q<69918 then
    if t.isSome then return {q:=q,mt:=1}
    return {q:=word ((q-69500)/209) ((q-69500)%209)}
  if 70000≤q && q<71024 then
    let v:=(q-70000)%512
    let side:=(q-70000)/512
    return {q:=if v<4 then (if side==0 then right else 71200) else 70000+512*side+v/2,wr:=some (some (v.testBit 0)),mr:=1}
  if q==71200 then
    if r.isSome then return {q:=left}
    return {q:=71201,mr:= -1,mt:=1}
  if q==71201 then
    if r.isSome then return {q:=q,mr:= -1}
    return {q:=71202,mr:=1}
  if 71202≤q && q<71211 then
    return {q:=q+1,wt:=some (some false),mt:=if q==71210 then -1 else 1}
  if q==71211 then
    if t.isSome then return {q:=q,mt:= -1}
    return {q:=71401,mt:=1}
  if 71401≤q && q<71912 then
    let v:=2*(q-71400)+(t.getD false).toNat
    if v<512 then return {q:=71400+v,mt:=1}
    if v==768 then return {q:=74900,mt:= -1}
    if v>767 then return fail
    return {q:=72000+v-512}
  if 72000≤q && q<74304 then
    let p:=(q-72000)/256
    let u:=(q-72000)%256
    return {q:=if p==8 then 75001 else q+256,ws:=some (some (p==0 || u.testBit (p-1))),ms:=1,wt:=some (some ((u+1).testBit p)),mt:= -1}
  if q==74900 then
    if t.isSome then return {q:=q,mt:= -1}
    return {q:=88000,mt:= -1}
  -- Three reader modes: first parent, second with first zero, second with first one.
  if 75000≤q && q<75768 then
    let z:=q-75000
    let v:=2*(z%256)+(r.getD false).toNat
    if v<256 then return {q:=75000+256*(z/256)+v,mr:=1}
    return {q:=76000+256*(z/256)+rev8 (v-256),mr:=1,ms:= -1}
  if 76000≤q && q<76768 then
    if s.isSome then return {q:=q,ms:= -1}
    return {q:=77000+q-76000,ms:=1}
  if 77000≤q && q<77768 then
    if s.isNone then return fail
    let z:=q-77000
    if z%256>0 then return {q:=q-1,ms:=1}
    if z/256==0 then return {q:=75001+256*(1+(s.getD false).toNat)}
    return {q:=78000+(!(z/256==2 && s==some true)).toNat}
  if q==78000 || q==78001 then
    if s.isSome then return {q:=q,ms:=1}
    return {q:=78002,ws:=some (some (q==78001)),ms:=1}
  if q==78002 then
    if r.isSome then return {q:=75001}
    return {q:=78101,mr:= -1,ms:= -1}
  if 78101≤q && q<78116 then
    let v:=2*(q-78100)+(s.getD false).toNat
    return {q:=if v≥16 then 78200+v-16 else 78100+v,ws:=some none,ms:= -1}
  if 78200≤q && q<78216 then
    if s.isSome then return {q:=q,ws:=some none,ms:= -1}
    return {q:=78300+q-78200,ms:=1}
  if 78300≤q && q<78316 then
    if r.isSome then return {q:=q,mr:= -1}
    return {q:=79000+16*(q-78300),mt:= -1}
  if 79000≤q && q<79256 then
    let z:=q-79000
    if t.isSome then
      if z%16==15 then return fail
      return {q:=q+1,mt:= -1}
    return {q:=80000+z,mt:=1}
  if 80000≤q && q<80256 then
    if t.isSome then return {q:=q,mt:=1}
    let z:=q-80000
    if z%16==0 then return {q:=81000+8*(z/16)}
    return {q:=82000+z,mr:= -1}
  if 81000≤q && q<81128 then
    let p:=(q-81000)%8
    let tag:=(q-81000)/8
    return {q:=if p==7 then 82000+16*tag else q+1,mr:=if p==7 then -1 else 0,out:=some (p%2==0 || tag.testBit (p/2))}
  if 82000≤q && q≤82255 then
    if q>82000 then return {q:=q-1,mr:= -1}
    return {q:=82256,wr:=some (some true),mr:=1}
  if q==82256 then
    if r.isSome then return {q:=q,mr:=1}
    return {q:=71401,mr:=1,mt:=1}
  if 88000≤q && q<88016 then
    if t.isSome then return {q:=q+1,mt:= -1}
    return {q:=88100+(q-88000),wt:=some (some true),mt:=1}
  if 88100≤q && q<88116 then
    if t.isSome then return {q:=q,mt:=1}
    return {q:=if q==88115 then 120000 else left}
  return fail
end VariableTagFront
namespace VariableTagFront
open SigabaNeo

def suffixPair (g : Nat) : Nat × Nat := Id.run do
  if g<3500 then
    let j:=(g-3200)/5
    let p:=(g-3200)%5
    let x:=325+j%4
    let y:=125+200*(2+j/4)+j%4
    let base:=3329+5*j
    if p==0 then return (x,y)
    if p==1 then return (x,base)
    if p==2 then return (y,base)
    if p==3 then return (base+1,base+2)
    return (base+3,base+3)
  if g<3618 && (g-3500)%2==0 then
    let j:=(g-3500)/2
    return (if j==0 then 3333 else 128+g,3333+5*(j+1))
  return (128+g,128+g)

def suffixRun (j : Nat) : Nat :=
  if j==1792 then 0 else
  let ab:=suffixPair (3200+j/2)
  if j%2==0 then 8*ab.1+3 else 4*ab.2+1

def stop := 229000
def clock := 5*2^28
def combined (q : Nat) (inp r s t : Option Bool) (coin : Bool) : A := Id.run do
  let reject : A := {q:=stop,out:=some false}
  if q<120000 then
    let a:=step q inp r s t
    return if a.q==bad then {a with q:=stop} else a
  if q<150481 then
    let v:=q-120000
    return {q:=q+1,wr:=some (if v%17==16 then none else some ((suffixRun (v/17)).testBit (v%17))),ws:=some (some true),mr:=1,ms:=1}
  if q==150481 then return {q:=150482,mr:= -1,ms:= -1}
  if q==150482 then
    if s.isSome then return {q:=q,mr:= -1,ms:= -1}
    return {q:=151000,mr:=1,ms:=1}
  if 151000≤q && q<184788 then
    let n:=q-151000
    if s.isNone then
      if inp==some true then return {q:=219000,mi:=1}
      return reject
    if inp==some true then
      if n==33787 then return reject
      return {q:=q+1,mi:=1}
    if inp.isNone then return reject
    return {q:=185000+n,mi:=1}
  if 185000≤q && q<218788 then
    let n:=q-185000
    if r.isNone then
      if n==0 then return {q:=151000,mr:=1,ms:=1}
      return reject
    if r != some (n.testBit 0) then return reject
    return {q:=185000+n/2,mr:=1,ms:=1}
  if q==219000 then
    if inp.isNone then return reject
    return {q:=219001,mi:=1}
  if q==219001 then
    if inp != some false then return reject
    return {q:=219002,mi:=1}
  if q==219002 then
    if inp.isSome then return reject
    return {q:=219003,mi:= -1}
  if q==219003 then return {q:=219004,mi:= -1,mr:= -1,ms:= -1}
  if q==219004 then
    if s.isSome then return {q:=q,wr:=some none,ws:=some none,mr:= -1,ms:= -1}
    return {q:=220000}
  if q==219005 then return {q:=220000+1025+17,mr:= -1}
  if 220000≤q && q<222273 then
    let z:=q-220000
    let p:=z-1025
    if z==1025+15 && t.isNone then return {q:=219005,mr:= -1,mt:= -1}
    let release:=(18≤p && p≤24) || p≥608
    let b:=if release then StreamBucketBank.transition 1024 513 16 z inp s t r coin
           else StreamBucketBank.transition 1024 513 16 z r s t inp coin
    let mr:=if release then (if b.mi==1 then (SignType.neg) else 0) else b.mr
    let a : A := {q:=220000+b.next,wr:=if release then none else b.wr,ws:=b.ws,wt:=b.wb,mr:=mr,ms:=b.ms,mt:=b.mb}
    if b.next≥2273 then return {a with q:=stop,out:=some false}
    if let some val:=b.emit then return {a with q:=224000+2*b.next+val.toNat,out:=some true}
    return a
  if 224000≤q && q<228546 then return {q:=220000+(q-224000)/2,out:=some (q%2==1)}
  return reject

def machine : Machine where
  tapes:=3
  states:=stop
  time:=clock
  machine:={
    initial:=⟨0,by decide⟩
    tr:=fun q inp w _ c=>
      let a:=combined q.val inp (w 0) (w 1) (w 2) c
      .step {
        inputTape:=a.mi
        workTapes:=fun i=>if i.val==0 then (a.wr,a.mr) else if i.val==1 then (a.ws,a.ms) else (a.wt,a.mt)
        output:=a.out
        state:=if h:a.q<stop then some ⟨a.q,h⟩ else none
      } Fin.elim0 Fin.elim0}

def decStep (q : Nat) (x : Option Bool) : StreamBucketBank.Step := Id.run do
  if q<514 then
    let a:=StreamBucketBank.framedAction (fun _=>0) q x
    if q≥4 && (q-4)%2==1 then
      let v:=2*((q-4)/2+1)+(x.getD false).toNat
      if v≥256 then return {next:=16000+2*rev8 (v-256),mi:=1}
    return a
  if q<16000 then return StreamBucketBank.framedAction (fun _=>0) q x
  if q<16512 then
    let z:=q-16000
    if z%2==1 then return {next:=q-1,mi:=1}
    if x==some true then return {next:=q+1,mi:=1}
    return {next:=16512+8*(z/2),mi:=1}
  if q<18600 then
    if q==16512 then return {next:=18600,mi:=0}
    return {next:=q-1,mi:=1}
  let p:=(q-18600)/16
  let tag:=(q-18600)%16+(if p%2==1 && x==some true then 2^(p/2) else 0)
  if p==7 then return {next:=546+2*tag,mi:=1}
  return {next:=18600+16*(p+1)+tag,mi:=1}

def decoder : Machine where
  tapes:=0
  states:=18728
  time:=2^28
  machine:={
    initial:=⟨0,by decide⟩
    tr:=fun q inp _ _ _ =>
      let a:=decStep q.val inp
      .step {
        inputTape:=a.mi
        workTapes:=Fin.elim0
        output:=a.emit
        state:=if h:a.next<18728 ∧ q.val != 15876 then some ⟨a.next,h.1⟩ else none
      } Fin.elim0 Fin.elim0}
end VariableTagFront

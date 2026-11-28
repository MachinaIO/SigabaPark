import SigabaNeo.Trusted.Machine

namespace StreamBucketBank
open SigabaNeo

/-- Three work tapes store template/positive secret, closing markers/negative
secret, and tagged six-bit bodies. The numeric phase intervals are disjoint. -/
structure Step where
  next : Nat
  wr : Option (Option Bool) := none
  ws : Option (Option Bool) := none
  wb : Option (Option Bool) := none
  mr : SignType := 0
  ms : SignType := 0
  mb : SignType := 0
  mi : SignType := 0
  emit : Option Bool := none

def rows (t k : Nat) := t+15*k
def states (n : Nat) := n+1249

/-- Exact on the supported positive templates, including initialization and both bank rewinds.
The substantive layout guarantee uses 0 < rows t k ≤ n and n > 0. -/
def ticks (n t k : Nat) := 5*n+rows t k*(7*n+44)+6*k+11

def transition (n t k q : Nat) (r s b inp : Option Bool) (coin : Bool) : Step := Id.run do
  if q=0 then return {next:=1,mr:=1,ms:=1,mb:=1}
  if q≤n then
    let j:=q-1
    return {next:=q+1,wr:=some (if j<rows t k then some (j≥t) else none), ws:=some (some (j≥t && (j-t)%15==14)),mr:=1,ms:=1}
  let p:=q-(n+1)
  let goto := fun (i : Nat) => n+1+i
  if p==0 then return {next:=goto 1,mr:= -1,ms:= -1}
  if p==1 then
    if s.isSome then return {next:=q,mr:= -1,ms:= -1}
    return {next:=goto 2,mr:=1,ms:=1}
  if p==2 then
    if r.isSome then return {next:=goto 3,wb:=some r,mb:=1}
    return {next:=goto 10,mr:= -1,ms:= -1,mb:= -1}
  if p==3 then return {next:=goto 4,wb:=some s,mb:=1}
  if p≤9 then
    let mv : SignType := if p==9 then 1 else 0
    return {next:=if p==9 then goto 2 else q+1,wb:=some (some false),mb:=1,mr:=mv,ms:=mv}
  if p==10 then
    if s.isSome then return {next:=q,mr:= -1,ms:= -1}
    return {next:=goto 11,mr:=1,ms:=1}
  if p==11 then
    if b.isSome then return {next:=q,mb:= -1}
    return {next:=goto 12,mb:=1}
  if p==12 then
    if s.isSome then return {next:=goto 13,wr:=some (some coin)}
    return {next:=goto 14,mr:= -1,ms:= -1}
  if p==13 then return {next:=goto 12,ws:=some (some coin),mr:=1,ms:=1}
  if p==14 then
    if r.isSome then return {next:=q,mr:= -1,ms:= -1}
    return {next:=goto 15,mr:=1,ms:=1}
  if p==15 then
    if b.isSome then return {next:=goto 16,mb:=1}
    return {next:=goto 17,mb:= -1,wr:=some (some (inp.getD false)),mi:=1}
  if p==16 then return {next:=goto 32,mb:=1}
  if p==17 then
    if b.isSome then return {next:=q,mb:= -1}
    return {next:=goto 608,mb:=1}
  -- Train-read phases: first skip the closing marker, then print six value bits.
  if p==18 then return {next:=goto 19,mb:=1}
  if p≤24 then return {next:=if p==24 then goto 608 else q+1,mb:=1,emit:=some (b.getD false)}
  if p<32 then return {next:=states n}
  -- Column control: six bit positions times 64 possible running residues.
  if p<416 then
    let j:=(p-32)/64
    let acc:=(p-32)%64
    if r.isNone then return {next:=goto (416+(acc+coin.toNat)%64)}
    let d:=if coin then 2^j*((r.getD false).toNat+63*(s.getD false).toNat) else 0
    let mv : SignType := if j==5 then 1 else 0
    return {next:=goto (32+64*((j+1)%6)+(acc+d)%64),mr:=mv,ms:=mv,emit:=some coin}
  if p<480 then
    let acc:=(p-416+63*coin.toNat)%64
    return {next:=goto (480+64+acc)}
  -- Value plus a seventh sentinel bit. The sentinel times exactly six writes.
  if p<608 then
    let word:=p-480
    let mv : SignType := if word<4 then -1 else 0
    return {next:=if word<4 then goto 14 else goto (480+word/2), wb:=some (some (word.testBit 0)),mb:=1,mr:=mv,ms:=mv}
  -- Decode the record kind while keeping only the share accumulator.
  if p<672 then
    if b.isNone then return {next:=states n}
    if b==some false then return {next:=goto 18,mb:=1}
    return {next:=goto (672+p-608),mb:=1}
  if p<736 then return {next:=goto (736+p-672),ws:=some b,mb:=1}
  if p<1120 then
    let j:=(p-736)/64
    let acc:=(p-736)%64
    let raw:=b.getD false
    let v:=(acc+63*2^j*raw.toNat)%64
    let next:=if j<5 then goto (736+64*(j+1)+v) else if s==some true then
      goto (1120+64+(v+32*(r.getD false).toNat)%64) else goto (608+v)
    return {next:=next,mb:=1,mi:=if j==5 then 1 else 0,emit:=some (inp.getD false && raw)}
  if p<1248 then
    let word:=p-1120
    return {next:=if word<4 then goto 608 else goto (1120+word/2), mi:=if word<4 then 1 else 0,emit:=some (inp.getD false && word.testBit 0)}
  return {next:=states n}

def machine (n t k : Nat) : Machine where
  tapes:=3
  states:=states n
  time:=ticks n t k
  machine:={
    initial:=⟨0,by simp [states]⟩
    tr:=fun q inp ws _ coin =>
      let a:=transition n t k q.val (ws 0) (ws 1) (ws 2) inp coin
      .step {
        inputTape:=a.mi
        workTapes:=fun i=>if i.val==0 then (a.wr,a.mr) else if i.val==1 then (a.ws,a.ms) else (a.wb,a.mb)
        output:=a.emit
        state:=if h : a.next < states n then some ⟨a.next,h⟩ else none
      } Fin.elim0 Fin.elim0}
end StreamBucketBank

namespace StreamBucketBank
open SigabaNeo

def fieldBits (n t k : Nat) := 6*n*rows t k+6*t+96*k

/-- A deterministic separate component for 16 tags. Input is four big-endian
tag bits followed by the issuer's entire ciphertext in its original order. -/
def localDecoder (n t : Nat) : Machine where
  tapes:=0
  states:=7728
  time:=4+fieldBits n t 16+1536+96+2
  machine:={
    initial:=⟨1, by decide⟩
    tr:=fun st a _ _ _ =>
      let q:=st.val
      let b:=(a.getD false).toNat
      let dest:=if q<16 then 2*q+b else
        if q<32 then (if a.isSome then q else 32+96*(32-q)-1) else
        if q<1568 then (if q==32 then 1568 else q-1) else
        let pos:=(q-1568)/64
        let v:=((q-1568)%64+b*2^(pos%6))%64
        if pos==95 then 7728 else 1568+64*(pos+1)+v
      let move : SignType := if q≥16 && q<32 && a.isNone then -1 else
        if q≥32 && q<1568 then (if q==32 then 0 else -1) else 1
      let out:=if q≥1568 && (q-1568)/64==95 then
        some ((((q-1568)%64+b*32)%64).testBit 5) else none
      .step {
        inputTape:=move
        workTapes:=Fin.elim0
        output:=out
        state:=if h : dest<7728 then some ⟨dest,h⟩ else none
      } Fin.elim0 Fin.elim0}
end StreamBucketBank

namespace StreamBucketBank
open SigabaNeo

/-- Original four-frame decoder for a fixed first-role lookup. It scans the
ciphertext frame to its terminator, then only counts backwards across the share tail. -/
def framedAction (tag : Nat → Fin 16) (q : Nat) (inp : Option Bool) : Step := Id.run do
  let b:=inp.getD false
  if q<4 then
    if q%2==1 then return {next:=q-1,mi:=1}
    if b then return {next:=q+1,mi:=1}
    return {next:=if q==0 then 2 else 4,mi:=1}
  if q<514 then
    let node:=(q-4)/2+1
    if (q-4)%2==0 then return {next:=q+1,mi:=1}
    let v:=2*node+b.toNat
    if v≥256 then
      let u:=(List.range 8).foldl (fun a i => a+(if v.testBit (7-i) then 2^i else 0)) 0
      return {next:=514+2*(tag u).val,mi:=1}
    return {next:=4+2*(v-1),mi:=1}
  if q<546 then
    let z:=q-514
    if z%2==1 then return {next:=q-1,mi:=1}
    if b then return {next:=q+1,mi:=1}
    return {next:=546+2*(z/2),mi:=1}
  if q<578 then
    let z:=q-546
    if z%2==1 then return {next:=q-1,mi:=1}
    if b then return {next:=q+1,mi:=1}
    return {next:=578+192*(16-z/2)-2,mi:= -1}
  if q<3650 then
    if q==578 then return {next:=3650,mi:=0}
    return {next:=q-1,mi:= -1}
  if q<15874 then
    let p:=(q-3650)/64
    let acc:=(q-3650)%64
    let v:=(acc+(if p%2==0 then b.toNat*2^((p/2)%6) else 0))%64
    if p==190 then return {next:=15874+(v==32).toNat,mi:=0,emit:=some true}
    return {next:=3650+64*(p+1)+v,mi:=1}
  if q<15876 then return {next:=15876,mi:=0,emit:=some (q==15875)}
  return {next:=15877,mi:=0,emit:=some false}

def framedDecoder (tag : Nat → Fin 16) : Machine where
  tapes:=0
  states:=15877
  time:=2^28
  machine:={
    initial:=⟨0,by decide⟩
    tr:=fun q inp _ _ _ =>
      let a:=framedAction tag q.val inp
      .step {
        inputTape:=a.mi
        workTapes:=Fin.elim0
        output:=a.emit
        state:=if h : a.next<15877 then some ⟨a.next,h⟩ else none
      } Fin.elim0 Fin.elim0}
end StreamBucketBank

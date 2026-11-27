import SigabaNeo.Trusted.Machine
import SigabaNeoStd.Lattices.LWE
import Mathlib.Tactic

namespace ShiftedDecisionTerminal
open SigabaNeo Turing

def params : Lattices.LWE.Params := ⟨512,1025,257,.cbd 1,.uniform,by decide⟩
noncomputable def premise : Assumption := Lattices.LWE.decision

/-- One step in the terminal ISA, with a physical input, two work heads and one output. -/
structure R where
  h : Nat := 0
  row : Nat := 0
  j : Nat := 0
  t : Nat := 0
  k : Nat := 0
  v : Nat := 0
  s : Nat := 0
  a : Nat := 0
  b : Bool := false
deriving Inhabited

structure A where
  next : Option R := none
  mi : Nat := 0
  m0 : Nat := 0
  m1 : Nat := 0
  w0 : Option Bool := none
  w1 : Option Bool := none
  o : Option Bool := none
deriving Inhabited

def wordBit (v i : Nat) : Bool := i<2*v.size && (i%2=0 || v.testBit (i/2))
def appendBit (v k : Nat) (b : Bool) := v + b.toNat * 2^k

/-- The message is one input symbol. The retained secret stays on tape zero and tape one buffers responses. -/
def issue (n m : Nat) (r : R) (input x y : Option Bool) (coin : Bool) : A := Id.run do
  let shift := if r.row+1=m && r.b then 128 else 0
  match r.h with
  | 0 => if let some b := input then return {next := some {h:=1,row:=m,b:=b},mi:=1} else return {}
  | 1 =>
    let v := appendBit r.v r.k coin
    if r.k<15 then return {next:=some {r with k:=r.k+1,v:=v}}
    if v=65535 && r.t<11 then return {next:=some {r with k:=0,v:=0,t:=r.t+1}}
    return {next:=some {r with h:=if r.row=m then 2 else 4,k:=0,t:=0,v:=v%257,s:=0}}
  | 2 =>
    let b := r.v.testBit r.k
    if r.k<8 then return {next:=some {r with k:=r.k+1},m0:=1,w0:=some b}
    if r.j+1<n then return {next:=some {r with h:=1,k:=0,j:=r.j+1,v:=0},m0:=1,w0:=some b}
    return {next:=some {r with h:=3,k:=0,j:=0,v:=9*n,row:=0},m0:=1,w0:=some b}
  | 3 => if r.v>0 then return {next:=some {r with v:=r.v-1},m0:=2}
         else return {next:=some {r with h:=1}}
  | 4 =>
    let s := appendBit r.s r.k (x.getD false)
    if r.k<8 then return {next:=some {r with s:=s,k:=r.k+1},m0:=1}
    return {next:=some {r with h:=5,k:=0,s:=0,a:=(r.a+s*r.v)%257},m0:=1}
  | 5 =>
    let b := r.k%4!=3 || wordBit r.v (r.k/4)
    if r.k+1<4*(2*r.v.size+1) then return {next:=some {r with k:=r.k+1},o:=some b}
    if r.j+1<n then return {next:=some {r with h:=1,k:=0,v:=0,j:=r.j+1},o:=some b}
    return {next:=some {r with h:=6,k:=0,v:=0,j:=0},o:=some b}
  | 6 => return {next:=some {r with h:=7,a:=(r.a+coin.toNat)%257},o:=some true}
  | 7 => return {next:=some {r with h:=8,a:=(r.a+257-coin.toNat+shift)%257},o:=some false}
  | 8 =>
    let b := r.a.testBit r.k
    if r.k<8 then return {next:=some {r with k:=r.k+1},w1:=some b,m1:=1}
    if r.row+1<m then return {next:=some {r with h:=3,k:=0,v:=9*n,row:=r.row+1,a:=0},w1:=some b,m1:=1}
    return {next:=some {r with h:=9,k:=0,v:=9*m,row:=0,a:=0},w1:=some b,m1:=1}
  | 9 => if r.v>0 then return {next:=some {r with v:=r.v-1},m1:=2}
         else return {next:=some {r with h:=10},o:=some false}
  | 10 =>
    let v := appendBit r.v r.k (y.getD false)
    if r.k<8 then return {next:=some {r with k:=r.k+1,v:=v},m1:=1}
    return {next:=some {r with h:=11,k:=0,v:=v},m1:=1}
  | 11 =>
    let b := wordBit r.v r.k
    if r.k<2*r.v.size then return {next:=some {r with k:=r.k+1},o:=some b}
    if r.row+1<m then return {next:=some {r with h:=10,k:=0,v:=0,row:=r.row+1},o:=some b}
    return {o:=some b}
  | _ => return {}

/-- Private input interface: nine little-endian bits per recovered secret coordinate, then the entire native packet. -/
def recover (n m : Nat) (r : R) (input x : Option Bool) : A := Id.run do
  let f := input.getD false
  match r.h with
  | 0 => if r.v+1<9*n then return {next:=some {r with v:=r.v+1},w0:=some f,m0:=1,mi:=1}
         else return {next:=some {r with h:=1,v:=9*n},w0:=some f,m0:=1,mi:=1}
  | 1 => if r.v>0 then return {next:=some {r with v:=r.v-1},m0:=2}
         else return {next:=some {r with h:=2}}
  | 2 => return {next:=some {r with h:=if f then 3 else 8,row:=if f then r.row else 0},mi:=1}
  | 3 => return {next:=some {r with h:=if f then 4 else 2,row:=if f then r.row else r.row+1},mi:=1}
  | 4 => return {next:=some {r with h:=5},mi:=1}
  | 5 =>
    if r.row+1!=m then return {next:=some {r with h:=2},mi:=1}
    if r.b then return {next:=some {r with h:=2,b:=false,v:=appendBit r.v r.k f,k:=r.k+1},mi:=1}
    if f then return {next:=some {r with h:=2,b:=true},mi:=1}
    return {next:=some {r with h:=6,k:=0,s:=0},mi:=1}
  | 6 =>
    let s := appendBit r.s r.k (x.getD false)
    if r.k<8 then return {next:=some {r with k:=r.k+1,s:=s},m0:=1}
    return {next:=some {r with h:=2,k:=0,v:=0,s:=0,a:=(r.a+s*r.v)%257},m0:=1}
  | 8 =>
    if f then return {next:=some {r with h:=9},mi:=1}
    if r.row+1<m then return {next:=some {r with row:=r.row+1},mi:=1}
    let d := (r.v+257-r.a)%257
    return {o:=some (127≤d && d≤129)}
  | 9 => return {next:=some {r with h:=8,k:=if r.row+1=m then r.k+1 else 0,v:=if r.row+1=m then appendBit r.v r.k f else 0},mi:=1}
  | _ => return {}

def dir (v : Nat) : SignType := if v=1 then 1 else if v=2 then -1 else 0

/-- A sentinel carries the length of a partially accumulated low-first word. -/
def prefixCode (k v : Nat) := 2^k+v
def suffixValue (c : Nat) := c-2^c.log2

/-- Phase-sensitive state codes avoid multiplying the rejection sampler by the exponent or word-output registers. -/
def issueCode (r : R) := Id.run do
  let data :=  match r.h with
    | 1 => 65536*r.t+prefixCode r.k r.v
    | 2 | 5 | 10 | 11 => r.v+257*r.k
    | 3 | 9 => r.v
    | 4 => r.v+257*prefixCode r.k r.s
    | 8 => r.k
    | _ => 0
  return r.h+16*(r.row+1026*(r.j+512*(r.b.toNat+2*(r.a+257*data))))

def issueReg (q : Nat) : R := Id.run do
  let h := q%16
  let u := q/16
  let w := u/1026/512/2
  let d := w/257
  let r : R := {h:=h,row:=u%1026,j:=u/1026%512,b:=u/1026/512%2=1,a:=w%257}
  match h with
  | 1 => return {r with t:=d/65536,k:=(d%65536).log2,v:=suffixValue (d%65536)}
  | 2 | 5 | 10 | 11 => return {r with v:=d%257,k:=d/257}
  | 3 | 9 => return {r with v:=d}
  | 4 => return {r with v:=d%257,k:=(d/257).log2,s:=suffixValue (d/257)}
  | 8 => return {r with k:=d}
  | _ => return r

def recoverCode (r : R) := Id.run do
  if r.h<2 then return r.h+16*r.v
  if r.h=6 then return r.h+16*(r.a+257*(r.v+257*prefixCode r.k r.s))
  return r.h+16*(r.row+1026*(r.a+257*(r.b.toNat+2*prefixCode r.k r.v)))

def recoverReg (m q : Nat) : R := Id.run do
  let h := q%16
  let u := q/16
  if h<2 then return {h:=h,v:=u}
  if h=6 then return {h:=6,row:=m-1,a:=u%257,v:=u/257%257,k:=(u/257/257).log2,s:=suffixValue (u/257/257)}
  let d := u/1026/257
  return {h:=h,row:=u%1026,a:=u/1026%257,b:=d%2=1,k:=(d/2).log2,v:=suffixValue (d/2)}

def assemble (k bits : Nat) (put : R → Nat) (get : Nat → R) (ticks : Nat) (fn : R → Option Bool → (Fin k → Option Bool) → Bool → A) : Machine where
  tapes := k
  states := 2^bits
  time := ticks
  machine := {
    initial:=⟨0,by positivity⟩
    tr:=fun q i w _ coin =>
      let act := fn (get q.val) i w coin
      let next := act.next.bind fun nr => if h : put nr < 2^bits then some ⟨put nr,h⟩ else none
      .step {inputTape:=dir act.mi,workTapes:=fun t =>
               ((if t.val=0 then act.w0 else act.w1).map some,dir (if t.val=0 then act.m0 else act.m1))
             output:=act.o,state:=next} (fun ii => Fin.elim0 ii) (fun ii => Fin.elim0 ii) }

def issuer : Machine := assemble 2 52 issueCode issueReg (2^28) fun r i w c => issue 512 1025 r i (w 0) (w 1) c

def decoder : Machine := assemble 1 33 recoverCode (recoverReg 1025) (2^27) fun r i w _ => recover 512 1025 r i (w 0)

theorem cost_local : issuer.cost + decoder.cost < 2^64 := by decide

theorem count_budget : (512*(1025+1)*192 + 512*9 + 1025*(512*(9+76)+2+9+9*512+1)+9*1025+1+1025*(9+19)+4 : Nat) < 2^28 ∧
    (9*512*2+1+1025*(76*512+2)+1+19*1025+9*512 : Nat) < 2^27 := by decide

theorem ambiguity_free : ∀ b : Bool, ∀ e : Fin 3,
    let d := (257+128*b.toNat+e.val-1)%257
    decide (127≤d ∧ d≤129) = b := by decide

theorem sampler_arithmetic : 65535=255*257 ∧ 512*(1025+1)<2^20 ∧ (512+1)*1025*9=4732425 := by decide

theorem mixture_gap (p₀ p₁ u : ℝ) : ((p₁+(1-p₀))/2 - (u+(1-u))/2) = (p₁-p₀)/2 := by ring
end ShiftedDecisionTerminal

namespace ShiftedDecisionTerminal
open SigabaNeo Turing

structure S where
  next : Option Nat := none
  move : Bool := false
  out : Option Bool := none
deriving Inhabited

def small (num clock : Nat) (positive : 0<num) (fn : Nat → Option Bool → Bool → S) : Machine where
  tapes := 0
  states := num
  time := clock
  machine := {initial:=⟨0,positive⟩
              tr:=fun q i _ _ coin =>
                let s := fn q.val i coin
                let next := s.next.bind fun u => if hu : u<num then some ⟨u,hu⟩ else none
                .step {inputTape:=if s.move then 1 else 0,workTapes:=fun t => Fin.elim0 t,
                       output:=s.out,state:=next} (fun t => Fin.elim0 t) (fun t => Fin.elim0 t)}

/-- Emits a private branch bit followed by the entire native packet shifted on that branch. -/
def shiftMap (m q : Nat) (input : Option Bool) (coin : Bool) : S := Id.run do
  if q=0 then return {next:=some (1+coin.toNat),out:=some coin}
  let b := (q-1)%2
  let p := (q-1)/2
  let go := fun t => some (1+2*t+b)
  let z := 2+2*(m-1)
  let emit := z+2050
  if p≥emit then
    let s := p-emit
    let v := s/2
    if v=0 then return {out:=some false}
    if s%2=0 then return {next:=go (p+1),out:=some true}
    return {next:=go (emit+2*(v/2)),out:=some (v%2=1)}
  let some f := input | return {}
  if p<2 then return {next:=go (if p=1 then 0 else if f then 1 else if m=1 then z+2 else 2),move:=true,out:=some f}
  if p<z then
    let t := (p-2)%2
    let next := if t=1 then p-1 else if f then p+1 else if p+2=z then z+2 else p+2
    return {next:=go next,move:=true,out:=some f}
  let c := (p-z)/2
  let top := 2^c.log2
  if (p-z)%2=1 then return {next:=go (z+2*(c+top*(1+f.toNat))),move:=true}
  if f then return {next:=go (p+1),move:=true}
  return {next:=go (emit+2*((c-top+128*b)%257)),move:=true}

/-- Removes the entire last matrix row and response, respecting all three native frames. -/
def prefixMap (m q : Nat) (input : Option Bool) : S := Id.run do
  let some f := input | return {}
  let base := 4*(m+1)
  if q<base then
    let i := q/4
    let h := q%4
    if h=0 && !f then return {next:=some base,move:=true,out:=some false}
    let next := if h=1 && !f then 4*(i+1) else 4*i+(h+1)%4
    return {next:=some next,move:=true,out:=if i+1<m then some f else none}
  let i := (q-base)/2
  if i+1≥m then return {}
  let h := (q-base)%2
  let next := if h=1 then q-1 else if f then q+1 else q+2
  return {next:=some next,move:=true,out:=some f}

def mixedPacket : Machine := small 10000 (2^26) (by decide) (shiftMap 1025)
def nativePrefix : Machine := small 6200 (2^26) (by decide) fun q i _ => prefixMap 1025 q i

theorem converters_cost : mixedPacket.cost+nativePrefix.cost < 2^28 := by decide

theorem ideal_shift (F : ZMod 257 → ℝ) (t : ZMod 257) :
    (∑ z, F (z+t)) = ∑ z, F z := Equiv.sum_comp (Equiv.addRight t) F
end ShiftedDecisionTerminal

namespace ShiftedDecisionTerminal

theorem accepted_fibers (u : Nat) (hu : u<65535) :
    u/257<255 ∧ u%257<257 ∧ 257*(u/257)+u%257=u := by omega

theorem all_fibers (i r : Nat) (hi : i<255) (hr : r<257) :
    257*i+r<65535 ∧ (257*i+r)/257=i ∧ (257*i+r)%257=r := by omega

/-- One quantitative certificate, conditional on the total charged reduction cost and the joint errors. -/
theorem transfer (g d e A B : ℝ) (hA : 1≤A) (he : 0≤e) (he' : e≤(2^67 : ℝ)⁻¹)
    (hgap : |g|≤2*|d|+e) (hhard : 2^166*d^2≤B) (hcost : B≤2^35*A) :
    2^128*g^2≤A := by
  have hs := mul_self_le_mul_self (abs_nonneg g) hgap
  have h1 : g^2≤6*d^2+3*e^2 := by
    nlinarith only [hs, sq_nonneg (|d|-e), sq_abs g, sq_abs d]
  have h2 := mul_self_le_mul_self he he'
  norm_num at hhard hcost h2 ⊢
  nlinarith only [h1,h2,hhard,hcost,hA]
end ShiftedDecisionTerminal

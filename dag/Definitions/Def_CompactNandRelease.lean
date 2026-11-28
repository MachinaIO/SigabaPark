import Definitions.Def_CompactRowMachines
import Definitions.Def_WE
import SigabaNeoStd.Machines.Gates
import Mathlib.Tactic

namespace CompactNandRelease201
open SigabaNeo Turing
open Packed201

abbrev Op := Option (Option Bool) × SignType
structure EAct where
  q : Option Nat := none
  mi : SignType := 0
  work : Fin 3 → Op := fun _ => (none,0)
  out : Option Bool := none

def moveAll (d : SignType) : Fin 3 → Op := fun _ => (none,d)
def putAll (v : Nat) (d : SignType) : Fin 3 → Op := fun t => (some (some (v.testBit t.val)),d)
def bits (w : Fin 3 → Option Bool) := ((w 0).getD true).toNat + 2*((w 1).getD true).toNat + 4*((w 2).getD true).toNat

/-- Before initializing the secret, all three tapes carry values of one public gate list on three assignments. -/
def front (inputs p : Nat) (i : Option Bool) (w : Fin 3 → Option Bool) : EAct := Id.run do
  if p=0 then return {q:=some (if i==some true then 1 else 2),mi:=1}
  if p=1 then return {q:=some 0,mi:=1}
  if 2≤p && p<2+inputs+1 then
    let j:=p-2
    let mask:=if j=0 then 7 else if j%2=1 then 6 else 2
    return {q:=some (if j=inputs then 140 else p+1),work:=putAll mask 1}
  if p=140 || p=141 then
    if i==some true then return {q:=some 142,mi:=1,work:=moveAll (-1)}
    return {q:=some (210+(p-140)),mi:=1,work:=moveAll (-1)}
  if p=142 then
    if (w 0).isSome then return {q:=some 142,work:=moveAll (-1)}
    return {q:=some 151,work:=moveAll 1}
  if 150≤p && p<158 then
    if i==some true then return {q:=some (150+(p-150+1)%8),mi:=1,work:=if p=157 && (w 0).isSome then moveAll 1 else moveAll 0}
    return {q:=some (160+bits w),mi:=1,work:=moveAll (-1)}
  if 160≤p && p<168 then
    if (w 0).isSome then return {q:=some p,work:=moveAll (-1)}
    return {q:=some (170+4*(p-160)),work:=moveAll 1}
  if 170≤p && p<202 then
    let a:=(p-170)/4
    let k:=(p-170)%4
    if i==some true then return {q:=some (170+4*a+(k+1)%4),mi:=1,work:=if k=3 && (w 0).isSome then moveAll 1 else moveAll 0}
    return {q:=some (202+(7 ^^^ (a &&& bits w))),mi:=1}
  if 202≤p && p<210 then
    if (w 0).isSome then return {q:=some p,work:=moveAll 1}
    return {q:=some (if p=202 then 140 else 141),work:=putAll (p-202) 1}
  if p=210 || p=211 then
    if (w 0).isSome then return {q:=some p,work:=fun _ => (some none,-1)}
    return {q:=some (p+2),work:=moveAll 1}
  if p=212 || p=213 then return {q:=some 256,mi:=1,work:=fun j => if j.val=1 then (some (some (p=213)),0) else (none,0)}
  return {}

abbrev EI := Packed201.CompactRowIssuer.Act
abbrev es := Packed201.CompactRowIssuer.states
abbrev ds := Packed201.CompactRowDecoder.states

/-- Only states with a physical output need a framing twin. -/
def emitCode (q : Nat) : Nat :=
  if q≥CompactRowIssuer.secretOut && q<CompactRowIssuer.multRead then q-CompactRowIssuer.secretOut
  else if q≥CompactRowIssuer.bodyOut then 257*85+(q-CompactRowIssuer.bodyOut)
  else if q=16003 then 257*104 else if q=16004 then 257*104+1 else 257*104+2

def emitPC (c : Nat) : Nat :=
  if c<257*85 then CompactRowIssuer.secretOut+c else if c<257*104 then CompactRowIssuer.bodyOut+c-257*85
  else if c=257*104 then 16003 else if c=257*104+1 then 16004 else CompactRowIssuer.noise

def enStates := 256+es+257*104+3

def en (n m inputs q : Nat) (i : Option Bool) (w : Fin 3 → Option Bool) (coin : Bool) : EAct := Id.run do
  if q<256 then return front inputs q i w
  let twin:=q≥256+es
  let pc:=if twin then emitPC (q-(256+es)) else q-256
  let a:=CompactRowIssuer.act n m pc i (w 0) (w 1) (w 2) coin
  let emitSecret := CompactRowIssuer.secretOut≤pc && pc<CompactRowIssuer.entryOut
  let o:=if emitSecret then some ((w 1).getD false && a.write.getD false) else a.emit
  if !twin && o.isSome then return {q:=some (256+es+emitCode pc),out:=some true}
  let skip:=CompactRowIssuer.rowRead≤pc && pc<CompactRowIssuer.rowWrite && a.next≥CompactRowIssuer.rowWrite && a.next<CompactRowIssuer.bodyRead
  let work := fun (j : Fin 3) =>
    if j.val=1 && pc=16001 && (w 0).isNone then (some (some false),0)
    else if j.val=a.tape then (a.write.map some,CompactRowIssuer.dir a.move)
    else if j.val=2 && skip then (none,1) else if j.val=1 && a.rewindSum then (none,-1) else (none,0)
  return {q:=if a.next<es then some (256+a.next) else none,work:=work,out:=if a.next≥es then some false else o}

def enc (n m inputs : Nat) : Machine where
  tapes:=3
  states:=enStates
  time:=465000000
  machine:={initial:=⟨0,by decide⟩
            tr:=fun q i w _ coin =>
              let a:=en n m inputs q.val i w coin
              let nq:=a.q.bind fun t => if h : t<enStates then some ⟨t,h⟩ else none
              .step {inputTape:=a.mi,workTapes:=a.work,output:=a.out,state:=nq} (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)}

def deStates := 12+2*ds

/-- The machine skips the three leading framed role fields and unframes ciphertext symbols on the input head. -/
def dec (n m : Nat) : Machine where
  tapes:=2
  states:=deStates
  time:=290000000
  machine:={initial:=⟨0,by decide⟩
            tr:=fun q i w _ _ => Id.run do
              let go:=fun (t : Nat) => if h : t<deStates then some (⟨t,h⟩ : Fin deStates) else none
              let step:=fun (next : Option (Fin deStates)) (mi : SignType) (out : Option Bool) =>
                MultiTapeMachine.Action.step {inputTape:=mi,workTapes:=fun _ => (none,0),output:=out,state:=next} (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
              let p:=q.val
              if p<6 then return step (go (if p%2=1 then p-1 else if i==some true then p+1 else p+2)) 1 none
              if p=6 then return step (go 12) 1 none
              if p=7 || p=8 then return step (go 9) 0 (some (p=8))
              if p=9 then return step none 0 (some false)
              if p≥12+ds then return step (go (p-ds)) 1 none
              let a:=CompactRowDecoder.decAct n m (p-12) i (w 0) (w 1)
              let nw:=fun (j : Fin 2) => if j.val=a.tape then (a.write.map some,CompactRowIssuer.dir a.move) else (none,0)
              let next:=if let some b:=a.out then go (7+b.toNat) else if a.next<ds then go (12+a.next+(if a.consume then ds else 0)) else none
              return .step {inputTape:=if a.consume then 1 else 0,workTapes:=nw,output:=a.out.map fun _ => true,state:=next} (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)}

theorem concrete_budget : (enc 512 1025 128).cost+(dec 512 1025).cost<2^32 := by decide

theorem dec_deterministic (n m : Nat) : (dec n m).Deterministic := by intro q i w a; rfl
end CompactNandRelease201
namespace CompactNandRelease201
open SigabaNeo
open AdvancedEncryption

def roles : Impl WE.sig where
  machine a := if a=WE.Alg.enc then enc 512 1025 128 else dec 512 1025
  deterministic a h := by
    by_cases ha : a=WE.Alg.enc
    · simp [WE.sig,ha] at h
    · simpa [ha] using dec_deterministic 512 1025

theorem role_cost : WE.cost roles < 2^32 := by decide
end CompactNandRelease201
namespace CompactTerminal201

def idleIssue (n m : Nat) : Nat :=
  9*n+1+(9*n+1)+1+10*m+1+(10*m+1)+(n+1)+192*n+9*n+
  m*(9*n+1)+n*m+192*n*m+27*n*m+m+9*m+9*m+(m-1)+(10*m+1)+(m+1)+9*m

theorem issue_count (n m : Nat) (hm : 1≤m) :
    idleIssue n m = 229*n*m+220*n+61*m+7 := by
  cases m with
  | zero => omega
  | succ k => simp only [idleIssue,Nat.succ_sub_one]; ring

def maxNative (n m : Nat) := m*(76*n+2)+1+19*m

theorem budget_all_lengths (L : Nat) (hL : L≤maxNative 512 1025) :
    L+idleIssue 512 1025≤160260698 ∧ L+45*512+11≤39929377 ∧
    1031+129+(2*(4096*(6*4224+3))+1)+4096*(3*4225+8)+4232+
       (L+idleIssue 512 1025)+L+9*512<465000000 ∧
    207643656+257+1+(L+45*512+11)+(9*512+L)+2<290000000 := by
  change L≤39906326 at hL
  rw [show idleIssue 512 1025=120354372 by decide]
  omega
end CompactTerminal201
namespace CompactNandRelease201
open SigabaNeo Turing.MultiTapeTM

def liftBits (w : List Bool) := w.flatMap fun b => [true,b]

theorem frame_eq (w : List Bool) : frame w=liftBits w++[false] := rfl

theorem lift_append (x y : List Bool) : liftBits (x++y)=liftBits x++liftBits y := by simp [liftBits]

theorem lift_ones (n : Nat) : liftBits (List.replicate n true)=List.replicate (2*n) true := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,liftBits,List.flatMap_cons,List.cons_append,List.nil_append] at ih ⊢; rw [ih,Nat.mul_succ]; rfl

theorem single_gate_code (a b : Nat) : liftBits (frame (encGate (a,b))) =
    List.replicate (8*a+3) true ++ [false] ++ List.replicate (4*b+1) true ++ [false] := by
  change liftBits (frame (frame (encUnary a) ++ encUnary b)) = _
  simp only [frame_eq,encUnary_apply,lift_append,lift_ones]
  simp only [List.append_assoc]
  rw [show 2*(2*(2*a))=8*a by omega,show 2*(2*b)=4*b by omega,
      List.replicate_add,List.replicate_add]
  simp [liftBits,List.append_assoc]
end CompactNandRelease201
namespace CompactTerminal201
open Packed201.CompactRowIssuer

def residueOf (s : Nat) (bits : List Bool) := bits.foldl (fun v c => (2*v+c.toNat)%257) s

def integerOf (s : Nat) (bits : List Bool) := bits.foldl (fun v c => 2*v+c.toNat) s

theorem sampler_fold (s : Nat) (bits : List Bool) : residueOf (s%257) bits=(integerOf s bits)%257 := by
  induction bits generalizing s with
  | nil => rfl
  | cons a bs ih =>
    change residueOf ((2*(s%257)+a.toNat)%257) bs = (integerOf (2*s+a.toNat) bs)%257
    simpa only [Nat.add_mod,Nat.mul_mod,Nat.mod_mod] using ih (2*s+a.toNat)

set_option maxRecDepth 20000 in
theorem boundary_samples : ∀ b : Bool,
    (act 512 1025 sample₀ none none none none b).next = sample₀+257+b.toNat ∧
    (act 512 1025 (sample₁+257*191+256) none none none none b).next = entryOut+76*((512+b.toNat)%257) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem field_frames : ∀ v : Fin 257,
    ((List.range (8*v.val.size+4)).map fun j => framedBit v.val j 3) =
      CompactNandRelease201.liftBits (CompactNandRelease201.liftBits (Turing.MultiTapeTM.frame v.val.bits)) ∧
    ((List.range (2*v.val.size+1)).map fun j => framedBit v.val j 1) = Turing.MultiTapeTM.frame v.val.bits := by decide
end CompactTerminal201

namespace CompactNandRelease201
set_option maxRecDepth 10000 in
theorem all_gate_payloads : ∀ a b : Fin 8,
    (front 128 (170+4*a.val) (some false) (fun k => some (b.val.testBit k.val))).q =
      some (202+(7 ^^^ (a.val &&& b.val))) := by decide
end CompactNandRelease201

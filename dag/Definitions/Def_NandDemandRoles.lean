import SigabaNeo.Trusted.Machine
import Mathlib
import SigabaNeoStd.Machines.Gates
namespace DemandRole
open SigabaNeo
structure Act where
  next : Nat
  inp : SignType := 0
  move : SignType := 0
  m0 : Option (Option Bool) := none
  m1 : Option (Option Bool) := none
  m2 : Option (Option Bool) := none
  m3 : Option (Option Bool) := none
  out : Option Bool := none
def op (next : Nat) (inp move : SignType := 0) : Act := ⟨next,inp,move,none,none,none,none,none⟩
def write (b : Bool) : Option (Option Bool) := some (some b)
def wipe : Option (Option Bool) := some none
def storeMask (r : Nat) : Option (Option Bool) := if r==3 then wipe else write (r==2)
def nandMask (p q : Nat) : Nat :=
  (if p != 1 && q != 1 then 1 else 0)+(if p != 2 || q != 2 then 2 else 0)
/-- 0 keep, 1 request left false, 2 request right false, 3 reject. A false gate requests both true. -/
def pick (need pl dl pr dr : Nat) : Nat :=
  if need==0 then 0
  else if need==1 then (if pl==1 || pr==1 || dl==1 || dr==1 then 3 else 0)
  else if dl==1 || dr==1 then 0
  else if dl==0 && pl==1 then 1
  else if dr==0 && pr==1 then 2
  else if dl==0 && pl != 2 then 1
  else if dr==0 && pr != 2 then 2 else 3
def act (q : Nat) (inp : Option Bool) (ws : Fin 4 → Option Bool) : Act :=
  let code:=q-1200
  let st:=code/54
  let beta:=code/27%2
  let need:=code/9%3
  let r:=code%9
  let ix:=fun (st b n r:Nat) => 1200+54*st+27*b+9*n+r
  let go:=fun s => ix s beta need r
  let rg:=fun s t => ix s beta need t
  let halt:=4818
  let bad:=op (ix 66 0 0 0)
  let origin:=ws 0 == some false
  let absent:=(ws 0).isNone
  let poss:=if absent then 2 else match ws 1 with | none => 3 | some false => 1 | some true => 2
  let dem:=match ws 2 with | none => 0 | some false => 1 | some true => 2
  let one:=inp==some true
  if q==0 then {op 1 0 1 with m0:=write false,m1:=write true}
  else if q≤128 then {op (q+1) 0 1 with m0:=write true}
  else if q==129 then (if origin then op 130 else op 129 0 (-1))
  else if q≤1160 then
    (if inp==some (!(q==643 || q==1157 || q==1159 || q==1160)) then
      op (if q==1160 then ix 0 0 0 0 else q+1) 1 else bad)
  else match st with
  | 0 => if one then op (go 1) 1 else if inp==some false then op (go 22) 1 else bad
  | 1 => if one then op (go 2) 1 else bad
  | 2 => if one then op (go 3) 1 else bad
  | 3 => if inp==some false then op (go 11) 1 else if one then op (go 4) 1 else bad
  | 4 => if one then op (go 5) 1 0 else bad
  | 5 => if one then op (go 6) 1 0 else bad
  | 6 => if one then op (go 7) 1 0 else bad
  | 7 => if one then op (go 8) 1 0 else bad
  | 8 => if one then op (go 9) 1 0 else bad
  | 9 => if one then op (go 10) 1 0 else bad
  | 10 => if one then op (go 3) 1 1 else bad
  | 11 => op (rg 12 poss)
  | 12 => if origin then op (go 13) else op (go 12) 0 (-1)
  | 13 => if one then op (go 14) 1 else bad
  | 14 => if inp==some false then op (go 18) 1 else if one then op (go 15) 1 else bad
  | 15 => if one then op (go 16) 1 0 else bad
  | 16 => if one then op (go 17) 1 0 else bad
  | 17 => if one then op (go 14) 1 1 else bad
  | 18 => op (rg 19 (nandMask r poss))
  | 19 => if origin then op (go 20) else op (go 19) 0 (-1)
  | 20 => if absent then {op (go 21) with m0:=write true, m1:=storeMask r} else op (go 20) 0 1
  | 21 => if origin then op (go 0) else op (go 21) 0 (-1)
  | 22 => if one then op (go 23) 1 else bad
  | 23 => if let some b:=inp then op (ix 24 b.toNat 0 0) 1 else bad
  | 24 => if inp==some false then op (go 25) 1 else bad
  | 25 => if inp.isNone then op (go 26) (-1) else bad
  | 26 => op (go 27) (-1)
  | 27 => op (go 28) (-1)
  | 28 => op (go 29) (-1)
  | 29 => op (go 30) (-1)
  | 30 => if absent then op (go 31) 0 (-1) else op (go 30) 0 1
  | 31 => if poss==1 then bad else {op (go 32) with m2:=write true}
  | 32 => {op (ix 33 beta dem 0) with m0:=wipe,m1:=wipe,m2:=wipe}
  | 33 => if origin then op (go 34) else op (go 33) 0 (-1)
  | 34 => if inp==some false then op (go 35) (-1) else bad
  | 35 => if one then op (go 36) (-1) else bad
  | 36 => if inp==some false then op (go 40) (-1) else if one then op (go 37) (-1) else bad
  | 37 => if one then op (go 38) (-1) 0 else bad
  | 38 => if one then op (go 39) (-1) 0 else bad
  | 39 => if one then op (go 36) (-1) 1 else bad
  | 40 => if absent then op (go 41) else op (go 42)
  | 41 => if origin then op (go 42) else op (go 41) 0 (-1)
  | 42 => {op (rg 43 ((poss-1)+3*dem)) with m3:=write true}
  | 43 => if origin then op (go 44) else op (go 43) 0 (-1)
  | 44 => if one then op (go 45) (-1) else bad
  | 45 => if one then op (go 46) (-1) else bad
  | 46 => if one then op (go 47) (-1) else bad
  | 47 => if inp==some false then op (go 55) else if one then op (go 48) (-1) else bad
  | 48 => if one then op (go 49) (-1) 0 else bad
  | 49 => if one then op (go 50) (-1) 0 else bad
  | 50 => if one then op (go 51) (-1) 0 else bad
  | 51 => if one then op (go 52) (-1) 0 else bad
  | 52 => if one then op (go 53) (-1) 0 else bad
  | 53 => if one then op (go 54) (-1) 0 else bad
  | 54 => if one then op (go 47) (-1) 1 else bad
  | 55 => if absent then op (go 56) else op (go 57)
  | 56 => if origin then op (go 57) else op (go 56) 0 (-1)
  | 57 => let pr:=r%3+1
      let dr:=r/3
      let action:=pick need poss dem pr dr
      if action==3 then bad
      else if need==1 then {op (rg 58 2) with m2:=write true}
      else if action==1 then {op (rg 58 0) with m2:=write false}
      else op (rg 58 (if action==2 then 1 else 0))
  | 58 => if origin then op (go 59) else op (go 58) 0 (-1)
  | 59 => if (ws 3).isSome then {op (go 60) with m3:=wipe,m2:=if r==0 then none else write (r==2)} else op (go 59) 0 1
  | 60 => if inp==some false then op (go 61) (-1) else bad
  | 61 => if one then op (go 62) 1 else if inp==some false then op (go 63) else bad
  | 62 => if absent then op (go 32) 0 (-1) else op (go 62) 0 1
  | 63 => {op (go 64) with out:=some true}
  | 64 => {op (go 65) with out:=some (beta==1)}
  | 65 => {op halt with out:=some false}
  | 66 => {op (ix 64 0 0 0) with out:=some true}
  | _ => bad

def enc : Machine where
  tapes:=4
  states:=4818
  time:=1000000000
  machine:={
    initial:=⟨0,by decide⟩
    tr:=fun q inp ws _ _ =>
      let a:=act q.val inp ws
      .step {inputTape:=a.inp,workTapes:=fun i =>
                   ((match i.val with | 0 => a.m0 | 1 => a.m1 | 2 => a.m2 | _ => a.m3),a.move),
             output:=a.out,state:=if h:a.next<4818 then some ⟨a.next,h⟩ else none}
             (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)}
def dec : Machine where
  tapes := 0
  states := 7
  time := 210000000
  machine := {
    initial := ⟨0,by decide⟩
    tr := fun q inp _ _ _ =>
      let i:=q.val
      let n:=if i==6 then 6 else if i%2==1 then i-1 else if inp==some true then i+1 else i+2
      .step {inputTape := 1,workTapes := Fin.elim0,
             output := if i==6 then inp else none
             state := if inp.isNone then none else if h : n<7 then some ⟨n,h⟩ else none}
            (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)}
end DemandRole
namespace DemandPolicy
open DemandRole
abbrev Map := Nat → Option Bool
def fits (t : Option Bool) (b : Bool) : Prop := t=none ∨ t=some b
def valid (r : Map) (v : Nat→Bool) := ∀ i,fits (r i) (v i)
def pcode : Option Bool→Nat | none=>3 | some false=>1 | some true=>2
def dcode : Option Bool→Nat | none=>0 | some false=>1 | some true=>2
def choice (need : Bool) (pl dl pr dr : Option Bool) (bit : Bool) :=
  if need && bit && pl.isNone && pr.isNone && dl.isNone && dr.isNone then 2 else
    pick (if need then 2 else 1) (pcode pl) (dcode dl) (pcode pr) (dcode dr)

theorem localChoice : ∀ (l r : Bool) (pl dl pr dr : Option Bool),
    fits pl l → fits pr r → fits dl l → fits dr r →
    ∃ c : Bool, let d:= !(l && r)
                let a:=choice d pl dl pr dr c
                a≠3 ∧ (d=false → l=true ∧ r=true) ∧
                 (d=true → (a=1 → l=false) ∧ (a=2 → r=false) ∧
                   (a=0 → dl=some false ∨ dr=some false)) := by
  unfold fits
  decide

def put (m : Map) (i : Nat) (b : Bool) : Map := fun j => if i=j then some b else m j
theorem putOk (m : Map) (v : Nat→Bool) (ok : valid m v) (i : Nat) :
    valid (put m i (v i)) v := by
  intro j; by_cases h : i=j
  · subst j; simp [put,fits]
  · simpa [put,h] using ok j

abbrev G := Nat×Nat×Nat
def next (p m : Map) (g : G) (c : Bool) : Option Map :=
  let (i,a,b):=g
  match m i with
  | none => some m
  | some d =>
    let k:=choice d (p a) (m a) (p b) (m b) c
    if k=3 then none else if !d then some (put (put m a true) b true)
    else if k=1 then some (put m a false) else if k=2 then some (put m b false) else some m

theorem one (p m : Map) (v : Nat→Bool) (i a b : Nat) (hp : valid p v) (hm : valid m v)
    (gate : v i= !(v a && v b)) : ∃ c m', next p m (i,a,b) c=some m' ∧ valid m' v := by
  cases h : m i with
  | none => exact ⟨false,m,by simp [next,h],hm⟩
  | some d =>
    have hd : d=v i := by
      have k:=hm i; simp [fits,h] at k; exact k
    obtain ⟨c,hk,hl,hr⟩ := localChoice (v a) (v b) (p a) (m a) (p b) (m b) (hp a) (hp b) (hm a) (hm b)
    have hd' : d= !(v a && v b) := hd.trans gate
    rw [←hd'] at hk hl hr
    refine ⟨c, if !d then put (put m a true) b true else if choice d (p a) (m a) (p b) (m b) c=1 then put m a false else if choice d (p a) (m a) (p b) (m b) c=2 then put m b false else m, ?_, ?_⟩
    · simp [next,h,hk]; split_ifs <;> rfl
    · cases d with
      | false =>
        obtain ⟨x,y⟩ := hl rfl
        simpa [x,y] using (putOk (put m a (v a)) v (putOk m v hm a) b)
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨ha,hb,_⟩ := hr rfl
        split
        · rename_i h1;simpa [ha h1] using putOk m v hm a
        · split
          · rename_i h2;simpa [hb h2] using putOk m v hm b
          · exact hm

def run (p : Map) : List G → List Bool → Map → Option Map
| [],_,m => some m
| g::gs,c::cs,m => (next p m g c).bind (run p gs cs)
| _::_,[],_ => none

theorem guided (p m : Map) (v : Nat→Bool) (gs : List G) (hp : valid p v) (hm : valid m v)
    (hg : ∀ g∈gs,v g.1= !(v g.2.1 && v g.2.2)) :
    ∃ cs m', cs.length=gs.length ∧ run p gs cs m=some m' ∧ valid m' v := by
  induction gs generalizing m with
  | nil => exact ⟨[],m,rfl,rfl,hm⟩
  | cons g gs ih =>
    obtain ⟨i,a,b⟩:=g
    obtain ⟨c,n,hs,hn⟩:=one p m v i a b hp hm (hg (i,a,b) (by simp))
    obtain ⟨cs,f,hlen,hf,hv⟩:=ih n hn (fun g h => hg g (by simp [h]))
    exact ⟨c::cs,f,by simp [hlen],by simp [run,hs,hf],hv⟩
end DemandPolicy
namespace DemandPolicy
open SigabaNeo DemandRole
def absNand (p q : Option Bool) : Option Bool :=
  match nandMask (pcode p) (pcode q) with
  | 1 => some false
  | 2 => some true
  | _ => none
theorem localUpper : ∀ (p q : Option Bool) (x y : Bool), fits p x → fits q y →
    fits (absNand p q) (!(x && y)) := by unfold fits; decide

theorem atWire (ps : List (Option Bool)) (xs : List Bool) (h : List.Forall₂ fits ps xs) (i : Nat) :
    fits (ps.getD i (some true)) (xs.getD i true) := by
  induction h generalizing i with
  | nil => simp [List.getD,fits]
  | cons h _ ih => cases i with
    | zero => simpa [List.getD] using h
    | succ i => simpa [List.getD] using ih i
def astep (ps : List (Option Bool)) (g : Nat×Nat) :=
  ps++[absNand (ps.getD g.1 (some true)) (ps.getD g.2 (some true))]
theorem snoc {ps : List (Option Bool)} {xs : List Bool} {m : Option Bool} {b : Bool} (h : List.Forall₂ fits ps xs) (k : fits m b) :
    List.Forall₂ fits (ps++[m]) (xs++[b]) := by
  induction h with
  | nil => exact .cons k .nil
  | cons f _ ih => exact .cons f ih

end DemandPolicy
namespace DemandPolicy
def tie (p m : Map) (g : G) : Bool :=
  (m g.1==some true) && g.2.1 != g.2.2 && (p g.2.1).isNone && (p g.2.2).isNone &&
    (m g.2.1).isNone && (m g.2.2).isNone

theorem skipBit (p m : Map) (g : G) (off : tie p m g=false) :
    next p m g false=next p m g true := by
  rcases g with ⟨i,a,b⟩
  cases hi : m i with
  | none => simp [next,hi]
  | some d =>
    cases d with
    | false => simp [next,hi,choice]
    | true =>
      by_cases h : (p a).isNone=true ∧ (p b).isNone=true ∧ (m a).isNone=true ∧ (m b).isNone=true
      · obtain ⟨h1,h2,h3,h4⟩:=h
        have eq : a=b := by simpa [tie,hi,h1,h2,h3,h4] using off
        have pa : p a=none := by simpa using h1
        have ma : m a=none := by simpa using h3
        subst b;simp [next,hi,choice,pa,ma,pcode,dcode,DemandRole.pick]
      · have hf : ((p a).isNone && (p b).isNone && (m a).isNone && (m b).isNone)=false := by
          cases h1 : p a <;> cases h2 : p b <;> cases h3 : m a <;> cases h4 : m b <;> simp_all
        simp [next,hi,choice,Bool.and_assoc] at *
        grind

def sparse (p : Map) : List G → List Bool → Map → Option Map
| [],_,m => some m
| g::gs,cs,m =>
   if tie p m g then match cs with
     | [] => none
     | b::bs => (next p m g b).bind (sparse p gs bs)
   else (next p m g false).bind (sparse p gs cs)

theorem compact (p m f : Map) (gs : List G) (cs : List Bool) (h : run p gs cs m=some f) :
    ∃ bs, bs.length≤gs.length ∧ sparse p gs bs m=some f := by
  induction gs generalizing m cs with
  | nil => exact ⟨[],by simp,by simpa [run,sparse] using h⟩
  | cons g gs ih =>
    cases cs with
    | nil => simp [run] at h
    | cons c cs =>
      cases hn : next p m g c with
      | none => simp [run,hn] at h
      | some n =>
        obtain ⟨bs,len,yes⟩:=ih n cs (by simpa [run,hn] using h)
        cases off : tie p m g with
        | true => exact ⟨c::bs,by simp [len],by simp [sparse,off,hn,yes]⟩
        | false =>
          have h0 : next p m g false=some n := by
            cases c with | false => exact hn | true => exact (skipBit p m g off).trans hn
          exact ⟨bs,by simp;omega,by simp [sparse,off,h0,yes]⟩
end DemandPolicy
namespace DemandPolicy
open SigabaNeo
def cert (need : List (Option Bool)) (prev : Option Bool) : GateList → List (Option Bool) → Prop
| [],[] => prev=some true
| (a,b)::gs,d::ds =>
    (d=some false → need.getD a (some true)=some true ∧ need.getD b (some true)=some true) ∧
    (d=some true → need.getD a (some true)=some false ∨ need.getD b (some true)=some false) ∧
    cert (need++[d]) d gs ds
| _,_ => False

theorem child_ok : ∀ (q l r : Option Bool) (x y : Bool), fits l x → fits r y →
    (q=some false → l=some true ∧ r=some true) →
    (q=some true → l=some false ∨ r=some false) → fits q (!(x && y)) := by
  intro q l r x y hl hr low high
  cases q with
  | none => exact Or.inl rfl
  | some b => cases b <;> cases x <;> cases y <;> simp_all [fits] <;> grind

end DemandPolicy

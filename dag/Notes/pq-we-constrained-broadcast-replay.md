---
title: Reproduce arbitrary boundary pins and the two-mark circuit matcher
refs: [note:pq-we-constrained-broadcast-separators, definition:SemSepRole]
tags: [witness-encryption, reproducibility]
---

Run pins192.py to compare against exhaustive trace enumeration and compute the full-size counts and exact residual widths. Run role192.py in the same folder to regenerate the two public machines. The final Lean listing may be appended to the role definition and run with lean --run, passing a binary file whose bytes 0 and 1 represent the successive *physical bits* on the registered input tape.

### pins192.py

```python
"""Counts accepting assignments extending arbitrary registered wire pins."""
from collections import defaultdict
from itertools import product
from random import Random

def template(k,n,labels=None):
    labels=list(range(1,k+1)) if labels is None else labels
    reps=labels.copy()
    gates=[]; origins={}
    def gate(a,b,tag):
        gates.append((a,b))
        z=n+len(gates)
        origins[z]=tag
        return z
    for i in range(k):
        for j in range(i+2,k):
            reps[j]=gate(reps[i],reps[j],('p',i+1,j))
    a=reps[0]
    for j in range(1,k):
        a=gate(a,reps[j],('a',j,0))
    gate(a,a,('z',k,0))
    return gates,origins

def recognize(k,n,circuit,labels):
    if len(labels)!=k or not all(0<=i<=n for i in labels):return False
    free=[i for i in labels if i]
    if len(set(free))!=len(free):return False
    want,_=template(k,n,labels)
    return len(circuit)==len(want) and all((a,b)==(x,y) or (a,b)==(y,x)
            for (a,b),(x,y) in zip(want,circuit))

def count(k,n,labels,pins):
    # Slots fixed to wire zero use value true. Other sources are distinct.
    g,origin=template(k,n,labels);total=0
    if pins.get(0,1)!=1:return 0
    if not all(0<=i<=n+len(g) for i in pins):raise ValueError('invalid wire')
    free=set(labels)-{0}
    unused=sum(i not in pins and i not in free for i in range(1,n+1))
    for h in range(k+1):
        early=[set([0,1]) for j in range(k)]
        late=[set([0,1]) for j in range(k)]
        acc=[set([0,1]) for j in range(k)]
        output=set([1]) # require acceptance as well as the explicit pins
        for j,src in enumerate(labels):
            if src==0:early[j]&={1}
            elif src in pins:early[j]&={pins[src]}
        for wire,bit in pins.items():
            if wire<=n:continue
            kind,r,j=origin[wire]
            if kind=='z':output&={bit}
            elif kind=='a':acc[r]&={bit}
            elif r<=h:early[j]&={bit^(r%2)}
            else:late[r-1]&={bit}
        states={(2,2,0):1}
        for i in range(k):
            nxt=defaultdict(int)
            for (old,new,a),num in states.items():
                for x in early[i]:
                    y=old>>x&1
                    if (i<h and not y) or (i==h and y):continue
                    u=(3^new) if y else 3
                    v=y if not i else 1-a*y
                    if (i>=h and (u&1) not in late[i]) or v not in acc[i]:continue
                    nxt[new,u,v]+=num
            states=nxt
        total+=sum(num for (_,_,a),num in states.items() if 1-a in output)
    return total<<unused

def trace(g,n,w):
    v=[1]+[w>>i&1 for i in range(n)]
    for a,b in g:v.append(1-v[a]*v[b])
    return v

def main():
    rng=Random(192)
    for k in range(2,10):
        n=k
        for t in range(45):
            labels=list(range(1,k+1));rng.shuffle(labels)
            labels=[x if rng.randrange(4) else 0 for x in labels]
            g,_=template(k,n,labels)
            g=[(y,x) if rng.getrandbits(1) else (x,y) for x,y in g]
            assert recognize(k,n,g,labels)
            pins={j:rng.randrange(2) for j in rng.sample(range(n+len(g)+1),rng.randrange(min(7,n+len(g)+2)))}
            expected=0
            for w in range(1<<n):
                v=trace(g,n,w)
                expected+=int(v[-1] and all(v[j]==b for j,b in pins.items()))
            assert count(k,n,labels,pins)==expected,(k,labels,pins)
    n=128;k=91;labels=list(range(1,k+1));g,_=template(k,n,labels)
    assert len(g)==4096
    baseline=count(k,n,labels,{})
    assert baseline>0 and baseline<1<<128
    for wire in [1,42,91,129,228,2150,4199,4223,4224]:
        assert sum(count(k,n,labels,{wire:b}) for b in (0,1))==baseline
    states=[{(2,2,0)}]
    def step(s,x,i):
        f,g,a=s;y=(f>>x)&1
        return g,(g^3 if y else 3),(y if i==0 else 1-a*y)
    for i in range(k):
        states.append({step(s,x,i) for s in states[-1] for x in (0,1)})
    cls={s:1-s[-1] for s in states[-1]};width=len(set(cls.values()))
    for i in reversed(range(k)):
        signature={s:tuple(cls[step(s,x,i)] for x in (0,1)) for s in states[i]}
        ids={p:j for j,p in enumerate(sorted(set(signature.values())))}
        cls={s:ids[p] for s,p in signature.items()};width=max(width,len(ids))
    assert width==4 and max(map(len,states))==5
    print('360 exhaustive pinned cases pass; 128-input K91 accepts exactly',baseline)
if __name__=='__main__': main()
```

### role192.py

```python
from itertools import groupby
from pathlib import Path
from pins192 import template,trace

def compile_program():
    g,_=template(91,128); assert trace(g,128,5)[-1]==1
    prog=[]
    def emit(k):prog.append(k);return len(prog)-1
    def ones(n):
        for _ in range(n//128):prog.extend([2,3,4])
        prog.extend([1]*(n%128))
    for a,b in g:
        a,b=sorted((2*a+1,2*b+1))
        ones(a)
        branch=emit(5)
        ones(b);emit(0)
        jump=emit(6)
        prog[branch]=5+16*len(prog)
        if a!=b:
            ones(b-a-1);emit(0);ones(a);emit(0)
        else:prog[branch]=0 # same numbers: require delimiter, process equal second run
        prog[jump]=6+16*len(prog)
    emit(7)
    return prog

def make(dest):
    prog=compile_program()
    # An instruction is op + 16*absolute jump target. RLE is source notation only.
    code=','.join(str(n)+':'+str(z) for z,vs in groupby(prog) for n in [len(list(vs))])
    p=len(prog);off=1130
    text='''import SigabaNeo.Trusted.Machine
namespace SemSepRole
open SigabaNeo
def ones (v : Array Nat) (n : Nat) : Array Nat := Id.run do
  let mut a:=v
  for _ in [:n/128] do a:=((a.push 2).push 3).push 4
  for _ in [:n%128] do a:=a.push 1
  return a
def ops : Array Nat := Id.run do
  let mut a:=#[]
  for t in "''' + ','.join(str(x*8192+y) for x,y in template(91,128)[0]) + '''".splitOn "," do
    let z:=t.toNat!
    let x:=2*(min (z/8192) (z%8192))+1
    let y:=2*(max (z/8192) (z%8192))+1
    a:=ones a x
    let branch:=a.size
    a:=a.push 5
    a:=(ones a y).push 0
    let jump:=a.size
    a:=a.push 6
    let dest:=a.size
    if x != y then
      a:=a.set! branch (5+16*dest)
      a:=(ones a (y-x-1)).push 0
      a:=(ones a x).push 0
    else a:=a.set! branch 0
    let dest:=a.size
    a:=a.set! jump (6+16*dest)
  return a.push 7
/-- A physical framing-bit recognizer with one tape holding two marks 64 cells apart. -/
def enc : Machine where
  tapes := 1
  states := STATES
  time := 35000000
  machine := {
    initial := ⟨0,by decide⟩
    tr := fun q inp ws _ _ =>
      let i:=q.val
      let pc:=i-1130
      let z:=ops[pc]?.getD 7
      let op:=z%16
      let mark:=(ws 0).isSome
      let one:=inp==some true
      let atOp:=i≥1130
      let err:=1100
      let next:= if i<65 then (if i==64 then 65 else i+1)
        else if i==65 then (if mark then 66 else 65)
        else if i<1096 then i+1
        else if i==1096 then 1130
        else if i==1100 then 1101 else if i==1101 then 1102
        else if i==1110 then 1111 else if i==1111 then 1112
        else if !atOp then 0
        else if op==0 then (if !one then i+1 else err)
        else if op==1 || op==2 then (if one then i+1 else err)
        else if op==3 then (if !one then err else if mark then i+1 else i)
        else if op==4 then (if mark then i+1 else if !one then err else i)
        else if op==5 then (if one then 1130+z/16 else i+1)
        else if op==6 then 1130+z/16
        else if !one then 1110 else err
      .step {inputTape := if i<66 || (atOp && (op==6 || (op==4 && mark))) then 0 else 1
             workTapes := fun _ =>
               if i==0 then (some (some true),1)
               else if i<64 then (none,1)
               else if i==64 then (some (some true),-1)
               else if i==65 && !mark then (none,-1)
               else if atOp && (op==2 || (op==3 && !mark)) then (none,1)
               else if atOp && ((op==3 && mark) || (op==4 && !mark)) then (none,-1)
               else (none,0)
             output := if i==1100 || i==1110 then some true
               else if i==1101 || i==1102 || i==1112 then some false
               else if i==1111 then some (inp.getD false) else none
             state := if i==1102 || i==1112 then none else
               if h : next < STATES then some ⟨next,h⟩ else none}
            (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)}
/-- Skip three framed input words and copy the final framed single-bit ciphertext. -/
def dec : Machine where
  tapes := 0
  states := 7
  time := 70000000
  machine := {
    initial := ⟨0,by decide⟩
    tr := fun q inp _ _ _ =>
      let i:=q.val
      let n:=if i==6 then 6 else if i%2==1 then i-1 else if inp==some true then i+1 else i+2
      .step {inputTape := 1,workTapes := Fin.elim0,
             output := if i==6 then inp else none
             state := if inp.isNone then none else if h : n<7 then some ⟨n,h⟩ else none}
            (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)}
end SemSepRole
'''
    states=p+off;dest.write_text(text.replace('STATES',str(states)))
    desc=18*states*(8+states.bit_length());print('states',states,'size',desc,'combined cost',desc+35000000+70000000+6*7*(4+3))
    print('RLE length',len(code))
if __name__=='__main__':make(Path(__file__).with_name('SemSepRole192.lean'))
```

### role-run192.leanpart

```lean
open SemSepRole
def runRoleEnc (word : ByteArray) : IO (Array Bool × Nat) := do
  let mut q:=enc.machine.initial
  let mut mem : Array (Option Bool) := Array.replicate 65 none
  let mut head:=0
  let mut pos:=0
  let mut out:=#[]
  for i in [:enc.time] do
    let inp:=(word[pos]?).map (· == 1)
    match enc.machine.tr q inp (fun _ => mem[head]!) Fin.elim0 false with
    | .query e _ => nomatch e
    | .step a _ _ =>
      let (wr,mv):=a.workTapes ⟨0,by decide⟩
      if let some z:=wr then mem:=mem.set! head z
      head:=match mv with | .pos => head+1 | .neg => head-1 | .zero => head
      if a.inputTape=1 then pos:=pos+1
      if let some b:=a.output then out:=out.push b
      match a.state with | none => return (out,i+1) | some z => q:=z
  throw (IO.userError "clock")
def main (args : List String) : IO Unit := do
  for file in args do
    IO.println (← runRoleEnc (← IO.FS.readBinFile file))
```

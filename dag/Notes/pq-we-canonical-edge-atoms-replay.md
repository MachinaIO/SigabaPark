---
title: Reproduce the sparse atom issuer, full-size tagged machines and reverse substitution experiment
refs: [note:pq-we-canonical-edge-atoms, definition:SparseAtomPair]
tags: [witness-encryption, algorithms, reproducibility]
---

Save the listings under their indicated names in the same directory. Run atoms-real186.py for the coefficient coupling and witness evaluations. Run python3 edge-machine186.py Def_SparseAtomPair.lean to regenerate the exact public machine definition and test the serial control against the direct ANF issuer. Run backward-nand-atoms.py separately for the adaptive dictionary experiment. The final Lean listing may be appended to the generated definition to execute both declared transitions on the two full-size variants, writing coefficient bytes to /tmp. It uses a fixed reproducible test coin sequence.

### atoms-real186.py

```python
from itertools import combinations
from random import Random
from collections import defaultdict,Counter
from hashlib import sha256
def variable(i):return frozenset((i,))
def F(*terms):return set(terms)
one=frozenset()
def xoradd(s,t):
 if t in s:s.remove(t)
 else:s.add(t)
def mul(f,g):
 h=set()
 for t in f:
  for w in g:xoradd(h,t|w)
 return h
def order(t):return tuple(sorted(t))
def layout(length,yes=False):
 n=128;chain=[0]+list(range(n,n+length));y=chain[-1];a=n+length;b=a+1;o=b+1
 gates=[(u,u,c) for u,c in zip(chain,chain[1:])]+[(0,y,a),((a if yes else y),(a if yes else 0),b),(a,b,o)]
 basis={one}
 for u,v,c in gates:
  scope={u,v,c}
  for j in range(1,len(scope)+1):basis.update(frozenset(ms) for ms in combinations(scope,j))
 for i in chain:basis.update((frozenset((0,i)),frozenset((0,a,i))))
 inc=defaultdict(list)
 for m in sorted(basis,key=order):
  for c in m:inc[c].append(m)
 atoms=[];flips=[];by=defaultdict(list)
 for i,(u,v,c) in enumerate(gates+[(None,None,o)]):
  cert=F(one,variable(c))
  if u is not None:
   xoradd(cert,frozenset((u,v)))
   fac=F(one) if i>=length else F(variable(0),frozenset((0,a)))
   if i==length+1:fac=F(variable(a))
   cert=mul(cert,fac)
  for m in inc[c]:
   g={m,m-{c}}
   if u is not None:xoradd(g,(m-{c})|{j for j in (u,v) if j<c})
   flips.append(int(m in cert));atoms.append(g)
   for t in g:by[t].append(len(atoms)-1)
 # Interleave the late gate's many atoms with the chain atoms by their variable index.
 globalw={0,y,a,b,o}
 def anchor(ts):return max((k for t in ts for k in t if k not in globalw),default=-1)
 perm=sorted(range(len(atoms)),key=lambda j:(anchor(atoms[j]),j))
 atoms=[atoms[j] for j in perm];flips=[flips[j] for j in perm];by=defaultdict(list)
 for j,g in enumerate(atoms):
  for t in g:by[t].append(j)
 # Sorted high-fan-in centers are visited once, followed by local output monomials ordered by median coin.
 rows=sorted(by,key=lambda t:(anchor([t]),by[t][len(by[t])//2],order(t)))
 p=0;dst=0;prog=[]
 for row in rows:
  seq=by[row];seq=seq if abs(seq[0]-p)<=abs(seq[-1]-p) else seq[::-1]
  for j,i in enumerate(seq):
   prog.append((i-p,j+1==len(seq),row==one));dst+=abs(i-p);p=i
 return gates,atoms,flips,rows,by,prog,dst
def enc(coins,beta,rows,by):
 return bytes((beta if m==one else 0)^(sum(coins[i] for i in by[m])%2) for m in rows)
def evaluate(ct,rows,z):return sum(x for x,m in zip(ct,rows) if all(z[j] for j in m))%2
def verify():
 rng=Random(186)
 for L in (3,4093):
  for yes in (False,True):
   gates,atoms,flips,rows,by,prog,dst=layout(L,yes)
   bits=bytes(rng.getrandbits(1) for _ in atoms)
   y0=enc(bits,0,rows,by);paired=enc(bytes(x^j for x,j in zip(bits,flips)),1,rows,by)
   if not yes:assert y0==paired
   for x in (0,1):
    z=[x]+[rng.getrandbits(1) for _ in range(127)]
    for u,v,c in gates:z.append(1-z[u]*z[v])
    assert bool(z[-1])==yes
    if yes:
     for b in (0,1):assert evaluate(enc(bits,b,rows,by),rows,z)==b
   print('length',L,'yes',yes,'atoms',len(atoms),'output',len(rows),'taps',len(prog),'moves',dst,'singletons',sum(len(v)==1 for v in by.values()),'SHA',sha256(y0).hexdigest())
if __name__=='__main__':verify()

```

### edge-machine186.py

```python
from importlib.machinery import SourceFileLoader as L
from pathlib import Path
from itertools import groupby
from random import Random
d=Path(__file__).parent
a=L('atoms',str(d/'atoms-real186.py')).load_module()
def compile():
 enc=[];dec=[];es=[];ds=[];et=[];dt=[]
 for yes in (False,True):
  gates,atoms,flips,rows,by,prog,dist=a.layout(4093,yes)
  es.append(len(enc));start=len(enc)
  enc.extend([2]*len(atoms));enc.extend([0]*len(atoms))
  for delta,final,constant in prog:
   enc.extend([int(delta>0)]*abs(delta));enc.append(3 if not final else 5 if constant else 4)
  enc.append(6);et.append(len(enc)-start+1)
  for x in (0,1):
   z=[x]+[0]*127
   for u,v,c in gates:z.append(1-z[u]*z[v])
   ds.append(len(dec));start=len(dec)
   dec.extend([2]*127)
   for t in rows:dec.append(int(all(z[j] for j in t)))
   dec.append(3);dt.append(len(dec)-start+2)
 return enc,dec,es,ds,et,dt
def runs(c):return [8*len(list(g))+k for k,g in groupby(c)]
def replay(c,h,nonce,beta):
 p=h;v=0;b=0;o=[];mem={};it=iter(nonce)
 while True:
  k=c[p];p+=1
  if k==6:return bytes(o),p-h+1
  if k==2:mem[v]=next(it);v+=1
  elif k<=1:v+=2*k-1
  else:
   b^=mem[v]
   if k>=4:o.append(b^(beta if k==5 else 0));b=0
def check(c,dc,es,ds):
 rng=Random(186)
 for yes in (False,True):
  gates,atoms,flips,rows,by,_,_=a.layout(4093,yes);coins=bytes(rng.getrandbits(1) for x in atoms)
  for beta in (0,1):
   ct,steps=replay(c,es[yes],coins,beta);assert ct==a.enc(coins,beta,rows,by)
   if not yes:
    y,_=replay(c,es[yes],bytes(x^j for x,j in zip(coins,flips)),1-beta);assert ct==y
   for x in (0,1):
    z=[x]+[1]*127
    for u,v,_ in gates:z.append(1-z[u]*z[v])
    bits=iter([1]*127+list(ct));v=0;i=ds[2*yes+x]
    while dc[i]!=3:
     k=dc[i];i+=1;t=next(bits)
     if k==1:v^=t
    assert v==a.evaluate(ct,rows,z)
    if yes:assert v==beta
def emit(dest):
 c,dc,es,ds,et,dt=compile();check(c,dc,es,ds)
 s='''import SigabaNeo.Trusted.Machine
namespace SparseAtomPair
open SigabaNeo
/-- Expand private source notation to the fixed local transition program.
Each positive run word is eight times its length plus the action code. -/
def expand (s : String) : Array Nat := Id.run do
  let mut a := #[]
  for t in s.splitOn "," do
    let n := t.toNat!
    for _ in [:n/8] do a := a.push (n%8)
  return a
'''
 for n,k in [('encOps',c),('decOps',dc)]:s+='def '+n+' : Array Nat := expand "'+','.join(map(str,runs(k)))+'"\n'
 se=2*len(c)+1;sd=2*len(dc)+3
 s+=f'''
/-- Input is the public fixture selector and the message; output is the canonical ANF coefficients. -/
def enc : Machine where
  tapes := 1
  states := {se}
  time := {max(et)}
  machine := {{
    initial := ⟨{se-1},by decide⟩
    tr := fun q inp ws _ coin =>
      let first := q.val == {se-1}
      let pc := q.val/2
      let op := encOps[pc]?.getD 6
      let b := xor (q.val%2==1) ((ws 0).getD false)
      let ns := if first then (if inp=some true then {2*es[1]} else 0)
        else 2*(pc+1)+(if op==3 then b else if op≤1 then q.val%2==1 else false).toNat
      .step {{ inputTape := if first then 1 else 0
              workTapes := fun _ => if first then (none,0)
                else if op==2 then (some (some coin),1) else if op==0 then (none,-1)
                else if op==1 then (none,1) else (none,0)
              output := if first then none else if op==4 then some b
                else if op==5 then some (xor b (inp.getD false)) else none
              state := if (!first && op==6) then none else if h : ns < {se} then some ⟨ns,h⟩ else none }}
            (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) }}
/-- Input is the selector, all 128 witness bits, and the canonical coefficient string. -/
def dec : Machine where
  tapes := 0
  states := {sd}
  time := {max(dt)}
  machine := {{
    initial := ⟨{sd-1},by decide⟩
    tr := fun q inp _ _ _ =>
      let first := q.val == {sd-1}
      let choose := q.val ≥ {sd-3}
      let pc := q.val/2
      let op := decOps[pc]?.getD 3
      let p := q.val%2==1
      let b := inp.getD false
      let ns := if first then (if b then {sd-2} else {sd-3})
        else if choose then (if q.val=={sd-2} then (if b then {2*ds[3]} else {2*ds[2]})
          else (if b then {2*ds[1]} else {2*ds[0]}))
        else 2*(pc+1)+(xor p (op==1 && b)).toNat
      .step {{ inputTape := if choose || op != 3 then 1 else 0
              workTapes := fun i => Fin.elim0 i
              output := if !choose && op==3 then some p else none
              state := if (!choose && op==3) then none else if h : ns < {sd} then some ⟨ns,h⟩ else none }}
            (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) }}
end SparseAtomPair
'''
 dest.write_text(s)
 print('enc',se,max(et),'dec',sd,max(dt),'tables',6*se*3*(8+se.bit_length()),6*sd*(4+sd.bit_length()),'sum',max(et)+max(dt)+6*se*3*(8+se.bit_length())+6*sd*(4+sd.bit_length()),len(s))
if __name__=='__main__':
 import sys
 emit(Path(sys.argv[1]))

```

### backward-nand-atoms.py

```python
"""Build a public linear mask space by substituting each live NAND wire backwards."""
from itertools import product
from random import Random

def substitute(term, output, a, b):
    rest=term ^ output
    return {rest} ^ {rest | a | b}

def plan(inputs,gates,budget):
    top=1<<(inputs+len(gates)-1)
    active={top}
    atoms=[{0,top}]
    visits=0
    for i in reversed(range(len(gates))):
        out=1<<(inputs+i)
        a,b=(1<<j for j in gates[i])
        changed=[term for term in active if term&out]
        visits+=len(active)
        if visits+len(atoms)+len(changed)>budget:
            return None
        for term in changed:
            atom={term} ^ substitute(term,out,a,b)
            active^=atom
            atoms.append(atom)
    return atoms,active,visits

def fixture(n,positive):
    return [(i,i) for i in range(n)]+[(0,n),(n,0),(n+1,0 if positive else n+2)]

def check(inputs,gates,budget):
    atoms,active,visits=plan(inputs,gates,budget)
    parity=set()
    columns=set()
    for atom in atoms:
        parity^=atom
        columns.update(atom)
    assert parity==({0} ^ active)
    for w in range(1<<inputs):
        vals=w
        for i,(a,b) in enumerate(gates):
            vals|=(1-((vals>>a)&(vals>>b)&1))<<(inputs+i)
        truth=lambda m:(m&vals)==m
        assert sum(truth(m) for m in active)%2==int(truth(1<<(inputs+len(gates)-1)))
        if truth(1<<(inputs+len(gates)-1)):
            assert all(sum(truth(m) for m in atom)%2==0 for atom in atoms)
    return len(atoms),len(columns|{0}),visits,len(active)

if __name__=='__main__':
    for positive in (False,True):
        print(positive,check(1,fixture(4093,positive),200000))
    rng=Random(186)
    for _ in range(200):
        gates=[tuple(rng.randrange(3+i) for _ in range(2)) for i in range(10)]
        check(3,gates,10000)
    print("200 mixed NAND fixtures checked.")

```

### edge-actual186.leanpart

```lean
open SparseAtomPair
def runEnc186 (tag beta : Bool) : IO (ByteArray × Nat) := do
  let mut q := enc.machine.initial
  let mut mem := Array.replicate 25000 false
  let mut h : Nat := 0
  let mut ip := 0
  let mut issued := 0
  let mut y := ByteArray.empty
  for step in [:enc.time] do
    let coin := (issued*43+7)%37 < 19
    let input := if ip==0 then tag else beta
    match enc.machine.tr q (some input) (fun _ => some mem[h]!) Fin.elim0 coin with
    | .query i _ => nomatch i
    | .step a _ _ =>
      let (write,mv) := a.workTapes ⟨0,by decide⟩
      if let some w := write then
        mem := mem.set! h (w.getD false)
        issued := issued+1
      h := match mv with | .pos => h+1 | .neg => h-1 | .zero => h
      if a.inputTape=1 then ip := ip+1
      if let some bit := a.output then y := y.push (bit.toNat.toUInt8)
      match a.state with | none => return (y,step+1) | some s => q := s
  throw (IO.userError "unterminated encoder")
def runDec186 (tag x : Bool) (ct : ByteArray) : IO (Bool × Nat) := do
  let mut q := dec.machine.initial
  let mut ip := 0
  for step in [:dec.time] do
    let inp := if ip==0 then tag else if ip==1 then x else if ip<129 then false else ct[ip-129]?.getD 0 == 1
    match dec.machine.tr q (some inp) Fin.elim0 Fin.elim0 false with
    | .query i _ => nomatch i
    | .step a _ _ =>
      if a.inputTape=1 then ip := ip+1
      match a.state with | none => return (a.output.getD false,step+1) | some s => q := s
  throw (IO.userError "unterminated decoder")
def replay186 : IO Unit := do
  for tag in [false,true] do
    for beta in [false,true] do
      let (ct,n) ← runEnc186 tag beta
      IO.FS.writeBinFile ("/tmp/edge186-"++toString tag++"-"++toString beta++".bin") ct
      for x in [false,true] do
        let (r,k) ← runDec186 tag x ct
        if tag && r != beta then throw (IO.userError "incorrect decryption")
        IO.println (tag,beta,x,n,k,ct.size,r)
#eval replay186

```

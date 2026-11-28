---
title: Reproduce quadratic cut, shear and native role experiments
refs: [note:nand-quadratic-cut, definition:ShearCutNativeRoles]
tags: [witness-encryption, reproducibility]
---

Run the Python blocks as separate files, then run the Lean driver with the generated .bin files to replay enc.machine.tr. Run Core.lean with a generated .gates source and output file to emit canonical bytes (optional final argument 1 selects a zero message). The role source in the DAG includes every fixed transition parameter.

### quadratic.py

```python
"""Exact simultaneous equations in independent Boolean NAND factor input pins."""
from itertools import product
from random import Random

def bits(x):
    while x:
        b=x & -x
        yield b
        x^=b

def toggle(s,x):
    if x in s:s.remove(x)
    else:s.add(x)

def mul(a,b):
    s=set()
    for x in a:
        for y in b:toggle(s,x|y)  # x_i squared reduces to x_i
    return s

def gauss(q,n):
    f=set(q);scale=1;remain=n
    while True:
        cross=next((m for m in f if m.bit_count()==2),None)
        if cross is None:
            return 0 if f-{0} else (-1 if 0 in f else 1)*scale*(1<<remain)
        x=cross & -cross;y=cross^x; f.remove(cross)
        l={m^x for m in f if m&x};r={m^y for m in f if m&y}
        f={m for m in f if not m&(x|y)} ^ mul(l,r)
        scale*=2;remain-=2

def count(k,rows):
    # Each row is (linear coefficient mask on 2k pins, selected products mask, RHS).
    # Product j is x_{2j} x_{2j+1}; constant one of NAND is absorbed into RHS.
    qbase={}; linear={}
    for a,q,t in rows:
        while q:
            j=q.bit_length()-1
            if j not in qbase:
                qbase[j]=(a,q,t);break
            u,v,c=qbase[j];a^=u;q^=v;t^=c
        if q:continue
        while a:
            j=a.bit_length()-1
            if j not in linear:
                linear[j]=(a,t);break
            u,c=linear[j];a^=u;t^=c
        if not a and t:return 0
    # Lift free pins to the whole common assignment, then substitute once in every row.
    var=[];free=0
    for j in range(2*k):
        if j not in linear:
            var.append({1<<free});free+=1
        else:
            a,t=linear[j];f={0} if t else set()
            for b in bits(a^(1<<j)): f^=var[b.bit_length()-1]
            var.append(f)
    prod=[mul(var[2*j],var[2*j+1]) for j in range(k)]
    qs=[]
    for a,q,t in qbase.values():
        f={0} if t else set()
        for b in bits(a):f^=var[b.bit_length()-1]
        for b in bits(q):f^=prod[b.bit_length()-1]
        qs.append(f)
    s=0;f=set();old=0
    for i in range(1<<len(qs)):
        gray=i^(i>>1)
        if i:f^=qs[(gray^old).bit_length()-1]
        old=gray;s+=gauss(f,free)
    assert s>=0 and s%(1<<len(qs))==0
    return s>>len(qs)

def accepts(k,rows,v):
    p=sum((((v>>(2*j))&3)==3)<<j for j in range(k))
    return all(((a&v).bit_count()^(b&p).bit_count()^t)&1==0 for a,b,t in rows)

def witness(k,rows):
    if count(k,rows)==0:return None
    given=list(rows);v=0
    for i in range(2*k):
        trial=given+[(1<<i,0,0)]
        if count(k,trial):given=trial
        else:given.append((1<<i,0,1));v|=1<<i
    assert accepts(k,rows,v)
    return v

def system(n,alpha,beta,target):
    assert n%2==0
    rows=[]
    # first n pairs (x,y); second n pairs (x',y'), U block [[1,1],[0,1]].
    for i in range(n):
        x=(1<<(2*(n+i)))^(1<<(2*i))
        y=(1<<(2*(n+i)+1))^(1<<(2*i+1))
        if i%2==0:x^=1<<(2*(i+1))
        else:y^=1<<(2*(i-1)+1)
        rows.extend([(x,0,alpha>>i&1),(y,0,beta>>i&1)])
    return rows+[(0,(1<<(2*n))-1,target)]

def circuit(n,alpha,beta,target):
    g=[]
    def nd(a,b):g.append((a,b));return 2*n+len(g)
    def neg(x):return nd(x,x)
    def xor(x,y):
        t=nd(x,y)
        return nd(nd(x,t),nd(y,t))
    x=[1+2*i for i in range(n)];y=[2+2*i for i in range(n)]
    full=[nd(a,b) for a,b in zip(x,y)]
    for i in range(n):
        a=xor(x[i],x[i+1]) if i%2==0 else x[i]
        b=xor(y[i-1],y[i]) if i%2 else y[i]
        if alpha>>i&1:a=neg(a)
        if beta>>i&1:b=neg(b)
        full.append(nd(a,b))
    out=full[0]
    for v in full[1:]:out=xor(out,v)
    if not target:out=neg(out)
    # Pad with unread NANDs *before* the final gate; no addresses change.
    last=g.pop();return g+[(0,0)]*(4095-len(g))+[last]

def eval_gate(g,v,n):
    a=[True]+[bool(v>>i&1) for i in range(2*n)]
    for x,y in g:a.append(not ((a[x] if x<len(a) else True) and (a[y] if y<len(a) else True)))
    return a[-1]

def main():
    rng=Random(213);checks=0
    for k in range(1,6):
        for _ in range(110):
            rows=[(rng.randrange(1<<(2*k)),rng.randrange(1<<k),rng.randrange(2)) for _ in range(rng.randrange(8))]
            assert count(k,rows)==sum(accepts(k,rows,v) for v in range(1<<(2*k)))
            if k<4: assert (witness(k,rows) is not None)==bool(count(k,rows))
            checks+=1
    for a,b,t in product(range(4),range(4),range(2)):
        rows=system(2,a,b,t);g=circuit(2,a,b,t)
        assert count(4,rows)==sum(eval_gate(g,v,2) for v in range(16))
    for a,b in [(0,0),(1<<63,0),(0,1),(rng.getrandbits(64),rng.getrandbits(64))]:
        for target in range(2):
            rows=system(64,a,b,target);g=circuit(64,a,b,target)
            num=count(128,rows);expected=(1<<127 if a or b else 0 if target else 1<<128)
            assert num==expected
            w=witness(128,rows)
            assert w is None or eval_gate(g,w,64)
    print(checks,'random systems; 32 small full-circuit counts; 8 rank-one 4096-gate counts and recovered positive witnesses')
if __name__=='__main__':main()
```

### fixture.py

```python
from pathlib import Path
def template(n=64):
 g=[]; optional=set()
 def nd(a,b):g.append((a,b));return 2*n+len(g)
 def xor(a,b):
  t=nd(a,b);return nd(nd(a,t),nd(b,t))
 x=[1+2*i for i in range(n)];y=[2+2*i for i in range(n)];z=[nd(a,b) for a,b in zip(x,y)]
 for i in range(n):
  a=xor(x[i],x[i+1]) if i%2==0 else x[i]
  b=xor(y[i-1],y[i]) if i%2 else y[i]
  optional.add(len(g));z.append(nd(a,b))
 p=z[0]
 for q in z[1:]:p=xor(p,q)
 last=g.pop();raw=len(g)
 g.extend([(0,0)]*(4095-len(g)));g.append(last)
 return g,optional,raw
g,optional,raw=template()
def frame(data):return bytes(z for b in data for z in (1,b))+bytes((0,))
prefix=frame(frame([1]*128)*2+frame([]))
assert [i for i,b in enumerate(prefix) if not b]==[513,1027,1029,1030]
runs=[];at=1031
for i,(a,b) in enumerate(g):
 for j,size in enumerate((8*a+3,4*b+1)):
  runs.append((at,size,((3,1)[j] if i in optional else -1)))
  at+=size+1
L=at
print(len(g),raw,len(optional),L,2*L+16,(2*L+16)*6*((2*L+16).bit_length()+4),L+12)
def mk(tag,flags,beta):
 gs=[(0 if i in optional and (i,0) in flags else a,0 if i in optional and (i,1) in flags else b) for i,(a,b) in enumerate(g)]
 out=prefix+b''.join(bytes((1,))*(8*a+3)+bytes((0,))+bytes((1,))*(4*b+1)+bytes((0,)) for a,b in gs)+bytes((0,1,beta,0))
 Path('/tmp/fault213-'+tag+'.bin').write_bytes(out)
 Path('/tmp/fault213-'+tag+'.gates').write_text(','.join(str(a*8192+b) for a,b in gs))
for key,flags,bt in [('intact',set(),1),('one',{(min(optional),0)},1),('many',{(j,1) for j in optional},0)]: mk(key,flags,bt)
```

### Replay.lean

```lean
import Definitions.Def_ShearCutNativeRoles
open ShearCutRole
def main (args : List String) : IO Unit := do
  for file in args do
    let bs ← IO.FS.readBinFile file
    let mut q:=enc.machine.initial
    let mut pos:=0
    let mut out:=#[]
    for i in [:enc.time] do
      let inp:=(bs[pos]?).map (· == 1)
      match enc.machine.tr q inp Fin.elim0 Fin.elim0 false with
      | .query e _ => nomatch e
      | .step a _ _ =>
        if let some b:=a.output then out:=out.push b
        if a.inputTape=1 then pos:=pos+1
        match a.state with
        | none => IO.println (out,i+1); break
        | some z => q:=z
```

### Core.lean

```lean
import Definitions.Def_WE_CircuitSAT
open SigabaNeo AdvancedEncryption AdvancedEncryption.WE Turing.MultiTapeTM
open AdvancedEncryption.WE.CircuitSAT
def proc200 (src dst : String) (variant : Nat) : IO Unit := do
  let a:=((← IO.FS.readFile src).splitOn ",").toArray.map String.toNat!
  if a.size != 4096 then throw (IO.userError "bad fixture")
  let g : Circuit 128 4096 := fun i =>
    let z:=a[i.val]!
    (⟨z/8192 %4225,Nat.mod_lt _ (by decide)⟩,⟨z%8192%4225,Nat.mod_lt _ (by decide)⟩)
  let R:=relation 128 4096
  let raw:=R.encStmt g
  let beta := variant%2==0
  let w:= if variant<2 then encodeTuple [paramsWord R params,raw,encBit beta]
          else encodeTuple [paramsWord R params,raw,R.encWit (fun i => i.val==0 || i.val==2),encBit beta]
  let buf:=w.foldl (fun (v:ByteArray) b => v.push b.toNat.toUInt8) ByteArray.empty
  IO.FS.writeBinFile dst buf
  IO.println (src,buf.size,variant)
def main (args : List String) : IO Unit := do
  match args with
  | [src,dst] => proc200 src dst 0
  | [src,dst,kind] => proc200 src dst kind.toNat!
  | _ => throw (IO.userError "supply fixture and output")
```

---
title: Reproduce common-observation projection and canonical tape checks
refs: [note:common-observation-projection, definition:LinearProjectNative]
tags: [witness-encryption, reproducibility]
---

Run compiler222.py, example.py, raw.py, polarity.py and spectral.py using python3. Run lake env lean --run Replay.lean on the generated .bin inputs. Run Core.lean with a .gates file and a destination to generate an independent input using the registered statement encoder. The final optional numeric argument 1 selects a zero message.

### compiler222.py

```python
"""A shared NAND-dag compiler. Affine leaves have a public retained-bit offset."""
from functools import lru_cache
from itertools import product
from random import Random

def rhs(a):return a.bit_count()%2
def reduce_row(x,basis):
 for row in basis:
    if x&(1<<(row.bit_length()-1)):x^=row
 return x
def basis(rows):
 b=[]
 for a in rows:
    a=reduce_row(a,b)
    if a:b=[r^a if r&(1<<(a.bit_length()-1)) else r for r in b]+[a];b.sort(reverse=True)
 return tuple(b)
def intersection(A,B):
 # Reduce A modulo B while tracking original combinations. Dependencies are exactly A intersect B.
 q=[];out=[]
 for a in A:
    x=reduce_row(a,B);track=a
    for v,t in q:
        if x&(1<<(v.bit_length()-1)):x^=v;track^=t
    if x:q.append((x,track));q.sort(reverse=True)
    else:out.append(track)
 return basis(out)
class BoolDAG:
 def __init__(self,k):
    self.k=k;self.nodes=[('const',0),('const',1)]+[('var',i) for i in range(k)];self.seen={}
 def nand(self,x,y):
    if x==0 or y==0:return 1
    if x==y==1:return 0
    x,y=sorted((x,y));key=(x,y)
    if key not in self.seen:self.seen[key]=len(self.nodes);self.nodes.append(('nand',key))
    return self.seen[key]
 def neg(self,a):return self.nand(a,a)
 def AND(self,a,b):return self.neg(self.nand(a,b))
 def OR(self,a,b):return self.nand(self.neg(a),self.neg(b))
 def any(self,vs):
    while len(vs)>1:vs=[self.OR(*vs[i:i+2]) if i+1<len(vs) else vs[i] for i in range(0,len(vs),2)]
    return vs[0]
 def value(self,id,z):
    a=[0,1]+[z>>i&1 for i in range(self.k)]
    for _,(p,q) in self.nodes[2+self.k:]:a.append(1^(a[p]&a[q]))
    return a[id]
def compile_cut(nodes,k,out):
 support=[]
 for n in nodes:
    support.append(basis([n[1]]) if n[0]=='leaf' else basis(support[n[1]]+support[n[2]]))
 # p encodes rows as (linear mask <<1) | prescribed value. Bit zero is reserved for RHS.
 def restrict(p,span):
    common=intersection(tuple(a>>1 for a in p),span)
    return tuple((r<<1)|reduce_row(r<<1,p) for r in common)
 peak=[0,0]
 def val(i,d,p):return go(i,d,restrict(p,support[i]))
 @lru_cache(None)
 def go(i,d,p):
    kind,a,b=nodes[i]
    if kind=='leaf':
        rem=reduce_row(a<<1,p)
        if rem>1:return 1
        return b if d^rem else out.neg(b)
    if a==b:return val(a,1-d,p)
    if d:return out.OR(val(a,0,p),val(b,0,p))
    fixed=tuple(t>>1 for t in p)
    # Images in quotient by the ancestor constraints must be intersected *after* restriction.
    A=basis(reduce_row(r,fixed) for r in support[a]);B=basis(reduce_row(r,fixed) for r in support[b])
    com=intersection(A,B);peak[0]=max(peak[0],len(com));peak[1]+=1<<len(com)
    bs=[]
    for t in range(1<<len(com)):
        cond=basis(p+tuple((r<<1)|(t>>j&1) for j,r in enumerate(com)))
        bs.append(out.AND(val(a,1,cond),val(b,1,cond)))
    return out.any(bs)
 root=val(len(nodes)-1,1,())
 return root,go.cache_info().currsize,peak

def evaluate(nodes,e,z):
 a=[]
 for kind,u,v in nodes:
    if kind=='leaf':a.append(rhs(u&e)^(v if v<2 else z>>(v-2)&1))
    else:a.append(1^(a[u]&a[v]))
 return a[-1]
def main():
 rng=Random(222);cases=0
 for ell in range(1,7):
    for _ in range(90):
      k=3;o=BoolDAG(k)
      nn=[('leaf',rng.randrange(1<<ell),rng.randrange(k+2)) for i in range(6)]
      for i in range(12):nn.append(('nand',rng.randrange(len(nn)),rng.randrange(len(nn))))
      r,m,p=compile_cut(nn,k,o)
      for z in range(1<<k):assert o.value(r,z)==any(evaluate(nn,e,z) for e in range(1<<ell))
      cases+=1
 # Before conditioning e and f are independent; after imposing e+f=0 they coincide.
 p=basis((3,));assert not intersection((1,),(2,))
 assert intersection(basis([reduce_row(1,p)]),basis([reduce_row(2,p)]))==(1,)
 print(cases,'DAGs, 4320 retained-input projections, explicit ancestor-induced correlation checked')
if __name__=='__main__':main()
```

### example.py

```python
from compiler222 import BoolDAG,compile_cut
from random import Random
def run(T):
    k=8;o=BoolDAG(k)
    table=[T>>i&1 for i in range(256)]
    for j in range(k):
        z=2+j;table=[o.nand(o.nand(o.neg(z),table[i]),o.nand(z,table[i+1])) for i in range(0,len(table),2)]
    a,b,c,d=[sum(1<<i for i in range(m,120,4)) for m in range(4)]
    nn=[('leaf',a^c,table[0]),('leaf',b^d,1),('leaf',a^b,1),('leaf',c^d,1)]
    def NAND(a,b):nn.append(('nand',a,b));return len(nn)-1
    def And(a,b):q=NAND(a,b);return NAND(q,q)
    And(And(0,1),And(2,3))
    beg=len(o.nodes);out,m,p=compile_cut(nn,k,o)
    assert [o.value(out,i) for i in range(256)]==[T>>i&1 for i in range(256)]
    return m,p,len(o.nodes)-beg
print([run(t) for t in [0,1<<253,2**256-1,Random(222).getrandbits(256)]])
```

### raw.py

```python
from pathlib import Path
from functools import reduce
def make(k=8):
 n=128;ell=(128-k);groups=[list(range(1+j,ell+1,4)) for j in range(4)]
 g=[];optional=set()
 def nd(a,b):g.append((a,b));return n+len(g)
 def inv(a):return nd(a,a)
 def conj(a,b):return inv(nd(a,b))
 def xor(a,b):
    t=nd(a,b);return nd(nd(a,t),nd(b,t))
 def tree(fn,ls):
    while len(ls)>1:ls=[fn(ls[i],ls[i+1]) if i+1<len(ls) else ls[i] for i in range(0,len(ls),2)]
    return ls[0]
 zero=nd(0,0)
 coins=[]
 for _ in range(1<<k):
    optional.add(len(g));coins.append(nd(0,zero))
 # flag gate second parent zero wire yields table true; replaced by wire 0 gives table false.
 z=[ell+i+1 for i in range(k)]
 for bit in z:
    neg=inv(bit)
    coins=[nd(nd(neg,coins[i]),nd(bit,coins[i+1])) for i in range(0,len(coins),2)]
 q=coins[0];p=[tree(xor,s) for s in groups]
 l1=xor(p[0],p[2]);l2=xor(p[1],p[3])
 r1=xor(p[0],p[1]);r2=xor(p[2],p[3])
 # left R requires l1=not q, l2=0 ; right requires r1=r2=0.
 left=conj(xor(l1,q),inv(l2));right=conj(inv(r1),inv(r2));conj(left,right)
 tail=g.pop();raw=len(g);g.extend([(0,0)]*(4095-len(g)));g.append(tail)
 return g,optional,raw
def frame(x):return bytes(v for b in x for v in (1,b))+bytes((0,))
prefix=frame(frame([1]*128)*2+frame([]))
def wire(g,b):return prefix+b''.join(bytes((1,))*(8*a+3)+bytes((0,))+bytes((1,))*(4*j+1)+bytes((0,)) for a,j in g)+bytes((0,1,b,0))
def variant(g,optional,table):return [(a,0 if i in optional and not (table>>(i-1)&1) else b) for i,(a,b) in enumerate(g)]
def eval_nand(g,v):
 w=[1]+[v>>i&1 for i in range(128)]
 for a,b in g:w.append(1^(w[a]&w[b]))
 return w[-1]
g,optional,raw=make();at=1031;runs=[]
for i,(a,b) in enumerate(g):
 for j,size in enumerate((8*a+3,4*b+1)):
    runs.append((at,size,1 if i in optional and j==1 else -1))
    at+=size+1
L=at
if __name__=='__main__':
 for name,tab,b in [('empty',0,1),('single',1<<253,1),('other',1<<241,0),('ones',(1<<256)-1,1)]:
    gs=variant(g,optional,tab)
    Path('/tmp/proj222-'+name+'.gates').write_text(','.join(str(a*8192+j) for a,j in gs))
    Path('/tmp/proj222-'+name+'.bin').write_bytes(wire(gs,b))
    for z in range(256):assert eval_nand(gs,z<<120)==(tab>>z&1)
 print(len(g),len(optional),raw,L,2*L+16)
```

### polarity.py

```python
from functools import cache
from itertools import product
from random import Random


def check(parents, inputs, retained):
    @cache
    def signs(v):
        if v < inputs:
            return {v: {1}}
        result = {}
        for parent in parents[v-inputs]:
            for i, polarities in signs(parent).items():
                result.setdefault(i, set()).update(-s for s in polarities)
        return result

    @cache
    def possible(v, target, fixed):
        values = dict(fixed)
        if v < inputs:
            return v not in values or values[v] == target
        left, right = parents[v-inputs]
        if target:
            return possible(left, 0, fixed) or possible(right, 0, fixed)
        if left == right:
            return possible(left, 1, fixed)
        a, b = signs(left), signs(right)
        conflicts = sorted(i for i in a.keys() & b.keys() - values.keys()
                           if len(a[i] | b[i]) > 1)
        for assignment in product((0, 1), repeat=len(conflicts)):
            conditioned = tuple(sorted((*fixed, *zip(conflicts, assignment))))
            if possible(left, 1, conditioned) and possible(right, 1, conditioned):
                return True
        return False

    v = inputs + len(parents)-1
    for z in product((0, 1), repeat=len(retained)):
        fixed = tuple(zip(retained, z))
        attained = set()
        for raw in product((0, 1), repeat=inputs):
            if any(raw[i] != value for i, value in fixed):
                continue
            trace = list(raw)
            for left, right in parents:
                trace.append(1-(trace[left] & trace[right]))
            attained.add(trace[v])
        assert all(possible(v, t, fixed) == (t in attained) for t in (0, 1))


if __name__ == "__main__":
    rng = Random(222)
    for _ in range(150):
        inputs = 6
        parents = [tuple(rng.randrange(inputs+i) for _ in range(2)) for i in range(18)]
        check(parents, inputs, (0, 1))
    print("matched 1200 projected truth values against full witness enumeration")
```

### spectral.py

```python
from collections import Counter
from itertools import combinations, islice, product


def rank(rows):
    pivots = {}
    for row in rows:
        while row:
            i = row.bit_length()-1
            if i not in pivots:
                pivots[i] = row
                break
            row ^= pivots[i]
    return len(pivots)


def masks(m, weight, count):
    return [sum(1 << i for i in support)
            for support in islice(combinations(range(m), weight), count)]


def lists(m, k):
    length = 1 << k
    a = [1 << i for i in range(m)] + masks(m, 4, length-m)
    b = [3 << i for i in range(m-1)] + masks(m, 3, length-m+1)
    assert len(set(a)) == len(set(b)) == length
    assert not set(a).intersection(b)
    assert rank(a) == rank(b) == m
    return a, b


def walsh_support(data):
    row = data.copy()
    w = 1
    while w < len(row):
        for i in range(0, len(row), 2*w):
            for j in range(i, i+w):
                row[j], row[j+w] = row[j]+row[j+w], row[j]-row[j+w]
        w *= 2
    return {i for i, v in enumerate(row) if v}


def condition_space(f, g):
    space = {0}
    while True:
        selected = next((a for a in sorted(f) if a not in space
                         and any((a ^ b) in space for b in g)), None)
        if selected is None:
            return space
        space.update({v ^ selected for v in space})


def check_fibers():
    domain = range(16)
    funcs = [[(x >> (i if (x >> s) & 1 else j)) & 1 for x in domain]
             for s in range(4) for i in range(4) for j in range(i+1, 4)
             if s not in (i,j)]
    spaces = {frozenset({0})}
    for a in domain:
        spaces |= {frozenset(u | {v ^ a for v in u}) for u in spaces}
    for f, g in product(funcs, repeat=2):
        fs, gs = walsh_support(f), walsh_support(g)
        space = condition_space(fs, gs)
        for u in spaces:
            if all(a in u or all((a ^ b) not in u for b in gs) for a in fs):
                assert space <= u
        fibers = {}
        for x in domain:
            label = tuple((x & a).bit_count() % 2 for a in sorted(space))
            fibers.setdefault(label, []).append(x)
        for fiber in fibers.values():
            joint = sum(f[x]*g[x] for x in fiber)
            assert joint*len(fiber) == sum(f[x] for x in fiber)*sum(g[x] for x in fiber)
    example_f = [(x >> (1 if x & 1 else 2)) & 1 for x in domain]
    example_g = [(x >> (0 if x & 2 else 3)) & 1 for x in domain]
    fs, gs = walsh_support(example_f), walsh_support(example_g)
    assert fs & gs == {0, 3}
    assert condition_space(fs, gs) == {0, 1, 2, 3}
    print("checked minimality across", len(spaces), "subspaces for", len(funcs)**2, "joins")


def check():
    a, b = lists(4, 2)
    for h, t in product(range(16), repeat=2):
        first, second = [], []
        for s in range(4):
            for y in range(16):
                first.append(((a[s] & y).bit_count() ^ (h >> s)) & 1)
                second.append(((b[s] & y).bit_count() ^ (t >> s)) & 1)
        assert set(Counter(zip(first, second)).values()) == {16}
        assert not (walsh_support(first) & walsh_support(second)) - {0}
    a, b = lists(120, 7)
    gates = sum(4*(v.bit_count()-1) for v in a+b) + 2*127*3+7+4
    assert gates == 1417
    print("256 offset pairs, 127-bit trivial period spaces, NAND upper bound", gates)


if __name__ == "__main__":
    check()
    check_fibers()
```

### Replay.lean

```lean
import Definitions.Def_LinearProjectNative
open LinearProjectRole
def main (args : List String) : IO Unit := do
  for path in args do
    let word←IO.FS.readBinFile path
    let mut q:=enc.machine.initial
    let mut ip:=0
    let mut wp:=0
    let mut mem:Array (Option Bool):=Array.replicate 18 none
    let mut out:=#[]
    for i in [:enc.time] do
      let sym:=mem[wp]!
      match enc.machine.tr q ((word[ip]?).map (·==1)) (fun _ => sym) Fin.elim0 false with
      | .query e _ => nomatch e
      | .step a _ _ =>
        let (wr,move):=a.workTapes ⟨0,by decide⟩
        if let some b:=wr then mem:=mem.set! wp b
        wp:=match move with | .pos=>wp+1 | .neg=>wp-1 | .zero=>wp
        if a.inputTape==1 then ip:=ip+1
        if let some b:=a.output then out:=out.push b
        match a.state with
        | none => IO.println (out,i+1);break
        | some nq => q:=nq
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

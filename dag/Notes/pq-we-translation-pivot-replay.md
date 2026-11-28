---
title: Reproducible source for the Boolean translation and guarded pivot experiments
refs: [note:pq-we-higher-degree-translation, definition:WE_CircuitSAT]
tags: [witness-encryption, reproducibility]
---
Save each code block under its heading in one directory. Run the cubic, Boolean translation, witness, affine action, XAG, and guarded scripts with Python 3. To check raw inputs under the registered relation run fixtures.py then compile rawCheck.lean with the DAG environment and run it on the six stems dense affine quartic quarticno cubic cubicno. Each gate file has 4,096 lines with two decimal wire references; each companion .w file holds the little-endian input mask as a decimal integer.

### quadratic-radical-quotient.py

```python
def kernel(rows,n):
    piv={}
    for row in rows:
        for j in sorted(piv,reverse=True):
            if row>>j&1:row^=piv[j]
        if not row:continue
        j=row.bit_length()-1
        for i in piv:
            if piv[i]>>j&1:piv[i]^=row
        piv[j]=row
    return ([ (1<<i)|sum(((row>>i)&1)<<j for j,row in piv.items())
              for i in range(n) if i not in piv],sorted(piv))
```

### quadratic-radical-raw.py

```python
from random import Random
def circuits(bad,degree=2,k=40,extra_tail=False):
    rng=Random(158); g=[];n=128
    def nand(i,j):
        g.append((i,j));return n+len(g)
    def NOT(i):return nand(i,i)
    def AND(i,j):return NOT(nand(i,j))
    def XOR(i,j):
        a=nand(i,j);return nand(nand(i,a),nand(j,a))
    def parity(xs):
        p=xs[0]
        for j in xs[1:]:p=XOR(p,j)
        return p
    w=list(range(1,129));t=w[:108]
    h=parity(t[42:] if degree==2 else t[70:74])
    for i in range(k):t[i]=XOR(t[i],h)
    tests=[]
    for i in range(k):
        prod=AND(t[i+1],t[i+2])
        if degree==3:prod=AND(prod,t[i+3])
        f=XOR(t[i],prod)
        tests.append(NOT(f) if rng.randrange(2) else f)
    if extra_tail:
        tests.append(NOT(XOR(AND(t[100],t[101]),AND(t[102],t[103]))))
    if bad:
        x,y,z=t[105:108]
        tests.extend([NOT(AND(x,y)),NOT(AND(x,z)),AND(y,z)])
    for _ in range(8*len(tests)):
        i,j=rng.sample(range(len(tests)),2);tests[i]=XOR(tests[i],tests[j])
    # Require each of the mixed quadratic outputs to vanish.
    pos=[NOT(v) for v in tests]
    # The last 20 inputs are uniquely determined once the first 108 are chosen.
    pos.extend(NOT(parity([w[108+i],w[4*i],w[4*i+1]])) for i in range(20))
    out=pos[0]
    for j in pos[1:]:out=AND(out,j)
    last=g.pop(); raw=len(g)+1
    assert raw<=4096
    g.extend([(4224,4224)]*(4095-len(g)));g.append(last)
    return g,raw

def extract(g,degree=2,return_anf=False):
    n=128;refs=[None]*129;xyz=[None]*129
    polys=[{0}]+[{1<<i} for i in range(n)]
    for a,b in g:
        i=len(refs);a=a if a<i else 0;b=b if b<i else 0
        refs.append((a,b));xor=None
        if refs[a] and refs[b]:
            for s in set(refs[a])&set(refs[b]):
                if refs[s] is None:continue
                x=refs[a][0]^refs[a][1]^s;y=refs[b][0]^refs[b][1]^s
                if sorted(refs[s])==sorted((x,y)):xor=(x,y);break
        xyz.append(xor)
        p,q=polys[a],polys[b]
        if xor is not None:
            x,y=xor;r=polys[x]^polys[y] if polys[x] is not None and polys[y] is not None else None
        elif a==b:r={0}^p if p is not None else None
        elif p is not None and q is not None and len(p)*len(q)<=10000:
            r={0}
            for x in p:
                for y in q:r.symmetric_difference_update((x|y,))
        else:r=None
        polys.append(r if r is None or all(k.bit_count()<=degree for k in r) else None)
    work=[(len(refs)-1,1)];guards=[]
    while work:
        i,bit=work.pop();p=polys[i]
        if p is not None:
            guards.append(p^({0} if bit else set()));continue
        a,b=refs[i]
        if a==b:work.append((a,bit^1))
        elif not bit:work.extend(((a,1),(b,1)))
        else:raise ValueError('unresolved')
    return guards
```

### boolean-translation-quotient.py

```python
"""Output-only projection for sparse ANFs with arbitrary degree; all variable labels stay fixed."""
from itertools import combinations
from pathlib import Path
from runpy import run_path
from random import Random
m=run_path(str(Path(__file__).with_name('quadratic-radical-quotient.py')))
ker=m['kernel']
def bits(v):
    while v:
        b=v&-v;yield b;v^=b
def combine(mask,vec):
    r=0
    for b in bits(mask):r^=vec[b.bit_length()-1]
    return r
def symcombine(mask,forms):
    r=set()
    for b in bits(mask):r^=forms[b.bit_length()-1]
    return r
def value(p,x):return sum(x&t==t for t in p)%2
def homogeneous(p,v,j):
    out=set()
    for mon in p:
        r=mon.bit_count()-j
        if r<=0:continue
        for removed in combinations(bits(mon&v),r):
            out.symmetric_difference_update((mon^sum(removed),))
    return out
def constant_dirs(fs,n):
    B=[1<<i for i in range(n)]
    deg=max((t.bit_count() for f in fs for t in f),default=0)
    for j in range(deg-1,0,-1):
        rows={}
        for i,v in enumerate(B):
            for h,f in enumerate(fs):
                for s in homogeneous(f,v,j):rows[h,s]=rows.get((h,s),0)^(1<<i)
        B=[combine(a,B) for a in ker(rows.values(),len(B))[0]]
    return B
def quotient(fs,n):
    tr=[]
    while fs:
        B=constant_dirs(fs,n)
        L=[sum((value(f,v)^int(0 in f))<<i for i,f in enumerate(fs)) for v in B]
        ann,piv=ker(L,len(fs))
        if not piv:break
        fs=[symcombine(mask,fs) for mask in ann];tr.append(len(piv))
    return fs,tr
def test():
    rng=Random(159)
    for _ in range(300):
        n=rng.randrange(1,7);fs=[{k for k in range(1<<n) if rng.randrange(6)==0} for _ in range(rng.randrange(1,7))]
        B=constant_dirs(fs,n)
        expected={v for v in range(1<<n) if all(all(value(f,x)^value(f,x^v)==value(f,v)^value(f,0) for x in range(1<<n)) for f in fs)}
        assert expected=={combine(s,B) for s in range(1<<len(B))}
        gs,tr=quotient(fs,n)
        count=lambda F:sum(not any(value(f,x) for f in F) for x in range(1<<n))
        assert count(fs)<<sum(tr)==count(gs)
    print('300 arbitrary-degree systems: entire constant-derivative group and exact count identity checked')
if __name__=='__main__':test()
```

### cubic-translation-raw.py

```python
from pathlib import Path
from runpy import run_path
p=Path(__file__).parent
raw=run_path(str(p/'quadratic-radical-raw.py'))
b=run_path(str(p/'boolean-translation-quotient.py'))
for bad in (False,True):
    k=12;n=128
    g,used=raw['circuits'](bad,3,k)
    fs=raw['extract'](g,3,True)
    assert max(t.bit_count() for f in fs for t in f)==3
    gs,tr=b['quotient'](fs,n)
    # All remaining forms involve at most the final three conflict variables.
    mask=0
    for f in gs:
        for t in f:mask|=t
    active=list(b['bits'](mask));assert len(active)<=3
    sol=sum(not any(b['value'](f,b['combine'](i,active)) for f in gs) for i in range(1<<len(active)))
    num=(sol<<(n-len(active)))//(1<<sum(tr))
    assert num==(0 if bad else 1<<(128-k-20))
    print(used,'gates padded to 4096;',len(fs),'constraints; projection ranks',tr,'remaining',len(gs),'number of witnesses',num)
```

### translation-witness-bijection.py

```python
"""A linear forward compiler and nonlinear reverse witness map for output-only elimination."""
from pathlib import Path
from runpy import run_path
from random import Random
b=run_path(str(Path(__file__).with_name('boolean-translation-quotient.py')))
def values(fs,x): return sum(b['value'](f,x)<<i for i,f in enumerate(fs))
def reduce_tagged(rows):
    basis={}
    for v,t in rows:
        for j in sorted(basis,reverse=True):
            if v>>j&1:
                w,s=basis[j];v^=w;t^=s
        if not v:continue
        j=v.bit_length()-1
        for k,(w,s) in list(basis.items()):
            if w>>j&1:basis[k]=(w^v,s^t)
        basis[j]=(v,t)
    return basis
def compile_system(fs,n):
    rounds=[];all_shifts=[]
    while fs:
        fs0=values(fs,0);K=b['constant_dirs'](fs,n)
        image=reduce_tagged((values(fs,r)^fs0,r) for r in K)
        if not image:break
        image_vectors=[w for w,t in image.values()]
        ann=b['ker'](image_vectors,len(fs))[0]
        rounds.append((fs,image))
        all_shifts.extend(t for w,t in image.values())
        fs=[b['symcombine'](a,fs) for a in ann]
    basis=reduce_tagged((r,0) for r in all_shifts)
    assert len(basis)==len(all_shifts)
    free=[i for i in range(n) if i not in basis]
    def project(w):
        for j,(r,_) in basis.items():
            if w>>j&1:w^=r
        return sum((w>>j&1)<<i for i,j in enumerate(free))
    def inject(z):
        return sum((z>>i&1)<<j for i,j in enumerate(free))
    def lift(z):
        w=inject(z)
        if values(fs,w):raise ValueError('child rejects')
        for prev,img in reversed(rounds):
            syndrome=values(prev,w)
            for j,(v,t) in img.items():
                if syndrome>>j&1:w^=t
            assert not values(prev,w)
        return w
    return len(free),project,inject,lift,fs
def small():
    rng=Random(159);yes=0;partial=0
    for _ in range(300):
        n=rng.randrange(2,9)
        f=[{m for m in range(1<<n) if rng.randrange(12)==0} for _ in range(rng.randrange(1,6))]
        if rng.randrange(2):
            f=[{m for m in p if m%2==0} for p in f]
            f[0]^={1}
        d,proj,inj,lift,gs=compile_system(f,n)
        old={w for w in range(1<<n) if not values(f,w)}
        child={z for z in range(1<<d) if not values(gs,inj(z))}
        assert {proj(w) for w in old}==child
        assert all(lift(proj(w))==w for w in old)
        assert all(proj(lift(z))==z for z in child)
        yes+=len(old);partial+=0<d<n and 0<len(child)<1<<d
    print('300 systems;',yes,'accepting witnesses round-tripped;',partial,'proper reductions with mixed child fibers')
if __name__=='__main__':small()
if __name__=='__main__':
    raw=run_path(str(Path(__file__).with_name('quadratic-radical-raw.py')))
    gates,used=raw['circuits'](False,3,12,True)
    f=raw['extract'](gates,3,True)
    d,project,inject,lift,g=compile_system(f,128)
    assert d==96 and len(g)==1
    # Substituting zero for eliminated coordinates only drops monomials.
    linear=[inject(1<<i).bit_length()-1 for i in range(d)]
    child={sum(((t>>j)&1)<<i for i,j in enumerate(linear)) for t in g[0] if all(not(t>>j&1) or j in linear for j in range(128))}
    support=sorted({b.bit_length()-1 for t in child for b in globals()['b']['bits'](t)})
    yes=sum(not globals()['b']['value'](child,sum((s>>i&1)<<j for i,j in enumerate(support))) for s in range(1<<len(support)))
    assert len(support)==4 and yes==6
    rng=Random(159);verified=0
    for _ in range(256):
        z=rng.getrandbits(d)
        if globals()['b']['value'](child,z):continue
        w=lift(z);v=[1]+[w>>i&1 for i in range(128)]
        for i,j in gates:v.append(1^((v[i] if i<len(v) else 1)&(v[j] if j<len(v) else 1)))
        assert v[-1] and project(w)==z
        verified+=1
    print(used,'unpadded gates; child dimension',d,'with one four-variable quadratic;',verified,'full registered witness round trips')
```

### affine-action-compiler.py

```python
"""Quotient an involutive input flip whose action on the syndrome is affine."""
from random import Random
from pathlib import Path
from runpy import run_path
base=run_path(str(Path(__file__).with_name('boolean-translation-quotient.py')))
value=base['value'];bits=base['bits']
def normal(p,B,tag=0):
    p=set(p)
    while p and (k:=max(p)) in B:
        r,c=B[k];p^=r;tag^=c
    return p,tag
def indy(fs):
    B={};basis=[]
    for f in fs:
        p,_=normal(f,B)
        if p:
            B[max(p)]=(p,0);basis.append(p)
    # An equation identically one in the row span rules out all solutions.
    return ([{0}] if 0 in B else basis)
def step(fs,j):
    fs=indy(fs)
    if fs==[{0}]:return None
    B={}
    for i,f in enumerate([{0}]+fs):
        r,c=normal(f,B,1<<i);B[max(r)]=(r,c)
    ds=[]
    for f in fs:
        delta={m^(1<<j) for m in f if m>>j&1}
        rem,code=normal(delta,B)
        if rem:return None
        ds.append(code)
    c=sum((code&1)<<i for i,code in enumerate(ds))
    if not c:return None
    pivot=(c&-c).bit_length()-1
    nxt=[]
    for i,f in enumerate(fs):
        if i!=pivot:nxt.append({m for m in (f^fs[pivot] if c>>i&1 else f) if not m>>j&1})
    return indy(nxt),fs[pivot],ds
def solve(fs,n):
    log=[];active=list(range(n));fs=indy(fs)
    while fs and fs!=[{0}]:
        for j in active:
            z=step(fs,j)
            if z:
                fs,p,d=z;log.append((j,p,d));active.remove(j);break
        else:break
    def proj(w):return sum(((w>>j)&1)<<i for i,j in enumerate(active))
    def inject(z):return sum(((z>>i)&1)<<j for i,j in enumerate(active))
    def lift(z):
        w=inject(z)
        if any(value(f,w) for f in fs):raise ValueError('reject')
        for j,p,_ in reversed(log):
            if value(p,w):w^=1<<j
        return w
    return fs,log,active,proj,inject,lift
def test():
    rng=Random(160);changed=0;hard=0
    for _ in range(400):
        n=rng.randrange(2,8)
        fs=[{m for m in range(1<<n) if rng.randrange(10)==0} for _ in range(rng.randrange(1,6))]
        if rng.randrange(2):
            f,g,h=[{m for m in range(0,1<<n,2) if rng.randrange(3)==0} for _ in range(3)]
            fs=[{1}^f,g,h^{m|1 for m in g}]
        rest,tr,active,proj,inj,lift=solve(fs,n)
        old={w for w in range(1<<n) if not any(value(f,w) for f in fs)}
        child={z for z in range(1<<len(active)) if not any(value(f,inj(z)) for f in rest)}
        assert {proj(w) for w in old}==child
        assert all(lift(proj(w))==w for w in old)
        changed+=bool(tr);hard+=bool(tr) and not base['quotient'](fs,n)[1]
    print('400 full fiber comparisons;',changed,'with eliminations,',hard,'where the constant-image test made no elimination')
if __name__=='__main__':test()
```

### affine-action-raw.py

```python
from pathlib import Path
from runpy import run_path
from random import Random
p=Path(__file__).parent
c=run_path(str(p/'affine-action-compiler.py'));raw=run_path(str(p/'quadratic-radical-raw.py'))
g=[]
def nand(x,y):g.append((x,y));return 128+len(g)
def inv(x):return nand(x,x)
def AND(x,y):return inv(nand(x,y))
def XOR(x,y):
    t=nand(x,y);return nand(nand(x,t),nand(y,t))
def direct(w):
    out=[1]+[w>>i&1 for i in range(128)]
    for i,j in g:out.append(1^((out[i] if i<len(out) else 1)&(out[j] if j<len(out) else 1)))
    return out[-1]
rs=[]
for h in range(16):
    x,u,v,y,z,a,b,w=range(8*h+1,8*h+9)
    guard=XOR(AND(y,z),AND(a,b))
    rs.extend((XOR(x,AND(u,v)),guard,XOR(AND(x,guard),AND(u,w))))
rng=Random(160)
for _ in range(8*len(rs)):
    i,j=rng.sample(range(len(rs)),2);rs[i]=XOR(rs[i],rs[j])
out=inv(rs[0])
for y in rs[1:]:out=AND(out,inv(y))
last=g.pop();used=len(g)+1;assert used<=4096
g.extend([(4224,4224)]*(4095-len(g)));g.append(last)
fs=raw['extract'](g,3,True)
rest,tr,active,proj,inject,lift=c['solve'](fs,128)
assert len(tr)==16 and len(active)==112
verified=0
valid=[w for w in range(256) if ((w>>0&1)==((w>>1&1)&(w>>2&1))) and ((w>>3&1)&(w>>4&1))==((w>>5&1)&(w>>6&1)) and not ((w>>1&1)&(w>>7&1))]
assert len(valid)==60
for _ in range(64):
    w=sum(rng.choice(valid)<<(8*i) for i in range(16))
    assert direct(w) and lift(proj(w))==w;verified+=1
print(used,'unpadded gates; 16 quotient pivots;',len(rest),'remaining equations; accepted count',60**16,';',verified,'witness round trips')
assert c['base']['constant_dirs'](fs,128)==[]
print('full cubic system has no nonzero constant-difference direction')
```

### xag-constant-directions.py

```python
"""Sufficient constant derivatives from live AND inputs in a shared XOR/AND DAG."""
from pathlib import Path
from runpy import run_path
from random import Random
b=run_path(str(Path(__file__).with_name('boolean-translation-quotient.py')))
def compile_xag(g,n):
    refs=[None]*(n+1);expr=[1]+[2<<i for i in range(n)];iscut=[False]*(n+1);atoms=[];unique={}
    for a,c in g:
        pos=len(refs);a=a if a<pos else 0;c=c if c<pos else 0;xor=None
        if refs[a] and refs[c]:
            for t in set(refs[a])&set(refs[c]):
                if not refs[t]:continue
                i=refs[a][0]^refs[a][1]^t;j=refs[c][0]^refs[c][1]^t
                if sorted(refs[t])==sorted((i,j)):xor=(i,j);break
        x=expr[a];y=expr[c]
        if xor:v=expr[xor[0]]^expr[xor[1]]
        elif not x or not y:v=1
        elif x==y or x==1 or y==1:v=1^(x if x==y or y==1 else y)
        elif x^y==1:v=1
        else:
            pair=tuple(sorted((x,y)))
            if pair not in unique:
                unique[pair]=len(atoms);atoms.append(pair)
            v=1|(1<<(1+n+unique[pair]))
        refs.append((a,c));expr.append(v);iscut.append(xor is not None)
    todo=[(len(g)+n,1)];seen=set();guards=[]
    while todo:
        i,v=todo.pop()
        if (i,v) in seen:continue
        seen.add((i,v))
        if refs[i] and not iscut[i]:
            x,y=refs[i]
            if x==y:todo.append((x,1^v));continue
            if not v:todo.extend(((x,1),(y,1)));continue
        guards.append(expr[i]^v)
    return guards,atoms
def solve(n,fs,atoms):
    raw=(1<<n)-1;trace=[]
    while fs:
        live=0
        for f in fs:live|=f>>(n+1)
        rows=[]
        for i in range(len(atoms)-1,-1,-1):
            if live>>i&1:
                for v in atoms[i]:
                    rows.append((v>>1)&raw);live|=v>>(n+1)
        B=b['ker'](rows,n)[0]
        cols=[sum(((((f>>1)&r).bit_count()%2)<<j) for j,f in enumerate(fs)) for r in B]
        ann,piv=b['ker'](cols,len(fs))
        if not piv:break
        trace.append((len(piv),live.bit_count()))
        fs=[b['combine'](a,fs) for a in ann]
    return fs,trace
def fixture():
    n=128;g=[]
    def nand(a,c):g.append((a,c));return n+len(g)
    def inv(x):return nand(x,x)
    def both(x,y):return inv(nand(x,y))
    def xor(x,y):
        t=nand(x,y);return nand(nand(x,t),nand(y,t))
    w=list(range(1,n+1));s=w[-1];suffix=[s]
    for x in w[-2::-1]:
        s=nand(inv(x),inv(s));suffix.append(s)
    suffix.reverse();fs=[xor(w[i],suffix[i+1]) for i in range(40)]
    rng=Random(159)
    for _ in range(320):
        i,j=rng.sample(range(40),2);fs[i]=xor(fs[i],fs[j])
    out=inv(fs[0])
    for f in fs[1:]:out=both(out,inv(f))
    last=g.pop();used=len(g)+1
    g.extend([(4224,4224)]*(4095-len(g)));g.append(last)
    return g,used
if __name__=='__main__':
    g,used=fixture();fs,atoms=compile_xag(g,128);remainder,tr=solve(128,fs,atoms)
    assert not remainder and sum(r for r,_ in tr)==40
    print(used,'unpadded gates;',len(fs),'constraints,',len(tr),'rounds;',2**(128-40),'solutions')
```

### guarded.py

```python
from random import Random


def basis(rows):
    table = {}
    for row in rows:
        p = set(row)
        while p and max(p) in table:
            p ^= table[max(p)]
        if p:
            table[max(p)] = p
    for lead in sorted(table):
        for other in table:
            if lead < other and lead in table[other]:
                table[other] ^= table[lead]
    return table


def reduces(p, table):
    p=set(p)
    while p and max(p) in table:
        p ^= table[max(p)]
    return not p


def mul_x(p, bit):
    answer=set()
    for m in p:
        answer.symmetric_difference_update([m|bit])
    return answer


def derivative(p, bit):
    return {m ^ bit for m in p if m & bit}


def evaluate(p, w):
    return sum(w&m==m for m in p) % 2


def eliminate(fs, active):
    fs=list(basis(fs).values())
    if {0} in fs:
        return None
    for j in active:
        bit=1<<j
        changes=[derivative(f,bit) for f in fs]
        piv=next((i for i,d in enumerate(changes) if 0 in d),None)
        if piv is None:
            continue
        q=fs[piv]
        gs=[f^q if 0 in changes[i] else f for i,f in enumerate(fs) if i!=piv]
        B=basis(gs)
        targets=[changes[piv]^{0}]+[derivative(f,bit) for f in gs]
        left=[t for t in targets if not reduces(t,B)]
        mult=None
        if left:
            for k in active:
                bigger=basis([*B.values(),*(mul_x(f,1<<k) for f in B.values())])
                if all(reduces(t,bigger) for t in left):
                    mult=k
                    break
            else:
                continue
        child=[{m for m in g if m&bit==0} for g in gs]
        return j,q,list(basis(child).values()),mult
    return None


def compile_system(fs,n):
    active=list(range(n));trace=[]
    while (step:=eliminate(fs,active)) is not None:
        j,q,fs,k=step
        active.remove(j);trace.append((j,q,k))
    def project(w):
        return sum(((w>>j)&1)<<i for i,j in enumerate(active))
    def lift(z):
        w=sum(((z>>i)&1)<<j for i,j in enumerate(active))
        assert not any(evaluate(f,w) for f in fs)
        for j,q,_ in reversed(trace):
            w^=evaluate(q,w)<<j
        return w
    return fs,active,trace,project,lift


def make_raw(power=4,bad=False):
    g=[];rs=[]
    def nand(x,y):
        g.append((x,y))
        return 128+len(g)
    def both(x,y):
        z=nand(x,y);return nand(z,z)
    def xor(x,y):
        z=nand(x,y);return nand(nand(x,z),nand(y,z))
    for block in range(16):
        x,u,v,y,z,a,b,w=range(8*block+1,8*block+9)
        h=xor(both(y,z),both(a,b)); xh=both(x,h)
        q=xor(x,both(u,v))
        if power==4:q=xor(q,both(xh,w))
        rs.extend([q,h,xor(xh,both(u,w))])
    if bad:
        # Force u=1 and v=1 while requiring uv=0.
        rs.extend([nand(2,2),nand(3,3),both(2,3)])
    rng=Random(160)
    for _ in range(8*len(rs)):
        i,j=rng.sample(range(len(rs)),2); rs[i]=xor(rs[i],rs[j])
    out=nand(rs[0],rs[0])
    for w in rs[1:]:
        out=both(out,nand(w,w))
    last=g.pop();used=len(g)+1
    g.extend([(4224,4224)]*(4095-len(g)));g.append(last)
    assert len(g)==4096 and all(0<=i<4225 and 0<=j<4225 for i,j in g)
    return g,used


def raw_value(g,w):
    v=[1]+[w>>i&1 for i in range(128)]
    for i,j in g:v.append(1^((v[i] if i<len(v) else 1)&(v[j] if j<len(v) else 1)))
    return v[-1]


def motif(w,power):
    x,u,v,y,z,a,b,w=[w>>i&1 for i in range(8)]
    h=(y&z)^(a&b)
    return x^(u&v)^((x&h&w) if power==4 else 0), h, (x&h)^(u&w)


def test(extract):
    for power in [3,4]:
        g,used=make_raw(power)
        fs=extract(g,power,True)
        child,active,tr,project,lift=compile_system(fs,128)
        assert len(tr)==16 and len(active)==112 and len(child)==32
        ok=[w for w in range(256) if not any(motif(w,power))]
        assert len(ok)==60
        assert all(len({tuple(a^b for a,b in zip(motif(w,power),motif(w^t,power)))
                         for w in range(256)})>1 for t in range(1,256))
        for w in range(256):
            expected=not any(motif(w,power))
            assert bool(raw_value(g,w))==expected
            if expected: assert lift(project(w))==w
        rng=Random(159)
        for _ in range(128):
            w=sum(rng.choice(ok)<<(8*i) for i in range(16))
            assert raw_value(g,w)==1 and lift(project(w))==w
        print(power,used,len(tr),sum(k is not None for _,_,k in tr),len(child),60**16)
    assert motif(24,4)==motif(152,4) and motif(25,4)!=motif(153,4)

if __name__=='__main__':
    from runpy import run_path
    from pathlib import Path
    test(run_path(str(Path(__file__).with_name('quadratic-radical-raw.py')))['extract'])
```

### fixtures.py

```python
from pathlib import Path
from runpy import run_path
p=Path(__file__).parent
get=lambda name:run_path(str(p/name))
raw=get('quadratic-radical-raw.py')
guard=get('guarded.py')
dense=get('xag-constant-directions.py')['fixture']()[0]
wc=get('translation-witness-bijection.py')['compile_system']
def emit(name,g,w):
    (p/(name+'.txt')).write_text(''.join(f'{a} {b}\n' for a,b in g))
    (p/(name+'.w')).write_text(str(w))
emit('dense',dense,(1<<128)-1)
for name,degree,bad,w in [('affine',3,False,0),('quartic',4,False,0),('quarticno',4,True,1)]:
    emit(name,guard['make_raw'](degree,bad)[0],w)
for bad in (False,True):
    g,_=raw['circuits'](bad,3,12)
    fs=raw['extract'](g,3,True)
    emit('cubicno' if bad else 'cubic',g,0 if bad else wc(fs,128)[3](0))
```

### rawCheck.lean

```lean
import Definitions.Def_WE_CircuitSAT
open AdvancedEncryption.WE.CircuitSAT
def readGate (s : String) : Option (Fin 4225 × Fin 4225) := do
  let [a,b] := s.splitOn " " | none
  let a ← a.toNat?
  let b ← b.toNat?
  if h : a<4225 ∧ b<4225 then return (⟨a,h.1⟩,⟨b,h.2⟩) else none
def main (args : List String) : IO Unit := do
  for path in args do
    let text ← IO.FS.readFile (path++".txt")
    let wtxt ← IO.FS.readFile (path++".w")
    let some w := wtxt.trimAscii.toString.toNat? | throw (IO.userError "invalid witness")
    let some gs := (text.trimAscii.toString.splitOn "\n").mapM readGate | throw (IO.userError "invalid gate")
    let g := gs.toArray
    if g.size != 4096 || w >= 2^128 then throw (IO.userError "wrong dimensions")
    let φ : Circuit 128 4096 := fun i => g[i.val]!
    let x : Fin 128 → Bool := fun i => w.testBit i.val
    let accepted := SigabaNeo.evalGates (List.ofFn x,φ.gates)
    IO.println s!"{path}: {accepted}"
```

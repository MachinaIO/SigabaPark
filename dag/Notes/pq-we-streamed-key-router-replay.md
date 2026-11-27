---
title: Reproducible transition and packet accounting for the static two-join router
refs: [note:pq-we-streamed-key-router, definition:StreamedRouterBlock]
tags: [witness-encryption, reproducibility]
---

Save the first listing as router.py and the second as packet.py in the same directory and run each with Python 3. The first replays each finite-control transition; the second evaluates selected honest routes and computes a seek ledger. The physical transition table is also provided in the definition node.



```python
from itertools import product
from collections import Counter
from struct import unpack,pack
from random import Random
from math import ceil
class Compiler:
    def __init__(self): self.p=[0]*6;self.code=[];self.labels={}
    def mark(self,name): self.labels[name]=len(self.code)
    def op(self,kind='move',args=(),moves=None):
        m=tuple((moves or {}).get(i,0) for i in range(6))
        self.code.append((kind,args,m))
        self.p=[x+d for x,d in zip(self.p,m)]
    def seek(self,targets):
        while any(self.p[i]!=x for i,x in targets.items()):
            self.op(moves={i:(x>self.p[i])-(x<self.p[i]) for i,x in targets.items()})
    def program(self):
        # physical logical heads: four array rows, scratch, dedicated input
        C=list(unpack('<4I',b'expand 32-byte k'))
        self.op('put',(4,None),{4:1})
        for _ in range(9): self.op('put',(4,1),{4:1})
        self.op('put',(4,None),{4:1});self.op(moves={4:1})
        for r in range(4):
            for i in range(128):
                if r in (1,2):
                    self.op('copy',(5,r),{5:1,r:1})
                else:
                    bit=((C[i//32]>>(i%32))&1) if r==0 else 0
                    self.op('put',(r,bit),{r:1})
        self.seek({i:0 for i in range(6) if i!=4})
        self.mark('pair')
        for k,j in product(range(2),range(4)):
            self.seek({r:32*((j+k*r)%4) for r in range(4)})
            for a,b,d,rot in ((0,1,3,16),(2,3,1,12),(0,1,3,8),(2,3,1,7)):
                u=self.p.copy()
                for i in range(32):
                    self.op('sumxor',(a,b,d,i==0),{a:1,b:1,d:1,4:1})
                self.seek({a:u[a],b:u[b],d:u[d]+rot-1,4:43})
                for i in range(32):
                    if i==rot:self.seek({d:u[d]+31})
                    self.op('copy',(4,d),{d:-1,4:-1})
                self.seek({d:u[d],4:12})
        self.seek({0:0,1:0,2:0,3:0,4:9})
        self.mark('find');self.op('find')
        self.mark('back');self.op('back')
        self.mark('again');self.op('jump',('pair',),{4:1})
        self.mark('exit');self.op('exit')
        self.mark('finish');self.op(moves={4:1})
        self.p=[0,0,0,0,12,0] # invariant of the preceding finite-state branches
        for r in range(4):
            for i in range(128):
                src='bus' if r in (1,2) else ((C[i//32]>>(i%32))&1 if r==0 else 0)
                self.op('feed',(r,src,i%32==0),{r:1,5:int(src=='bus')})
        self.seek({0:0,1:0,2:0,3:0,4:0})
        return self
def run(c,key):
    tape=[{} for _ in range(5)]+[{i:(key[i//8]>>(i%8))&1 for i in range(256)}]
    pos=[0]*6;out=[];pc=carry=ticks=0
    while pc<len(c.code):
        kind,args,mm=c.code[pc];m=list(mm);pc+=1;ticks+=1
        def rd(i):return tape[i].get(pos[i])
        def wr(i,v):tape[i][pos[i]]=v
        if kind=='put':wr(*args)
        if kind=='copy':a,b=args;wr(b,rd(a))
        if kind=='sumxor':
            a,b,d,reset=args;s=rd(a)+rd(b)+(0 if reset else carry)
            carry=s>>1;wr(a,s&1);wr(4,rd(d)^(s&1))
        if kind=='feed':
            r,src,reset=args;s=rd(r)+(rd(5) if src=='bus' else src)+(0 if reset else carry)
            carry=s>>1;out.append(s&1)
        if kind=='jump':pc=c.labels[args[0]]
        if kind=='find':
            z=rd(4)
            if z==0:pc=c.labels['find'];m[4]=-1
            elif z==1:wr(4,0);pc=c.labels['back'];m[4]=1
            else:pc=c.labels['exit'];m[4]=1
        if kind in ('back','exit'):
            m[4]=1
            pc=c.labels[kind if rd(4)==0 else ('again' if kind=='back' else 'finish')]
        pos=[v+e for v,e in zip(pos,m)]
    assert pos==[0,0,0,0,0,256] and len(out)==512
    return bytes(sum(out[8*i+j]<<j for j in range(8)) for i in range(64)),ticks
def reference(key):
    v=list(unpack('<16I',b'expand 32-byte k'+key+bytes(16)));x=v.copy()
    for k,j in product(range(20),range(4)):
        a,b,c,d=[4*r+(j+(k%2)*r)%4 for r in range(4)]
        for p,q,z,rot in ((a,b,d,16),(c,d,b,12),(a,b,d,8),(c,d,b,7)):
            x[p]=(x[p]+x[q])%2**32
            t=x[z]^x[p];x[z]=((t<<rot)|(t>>(32-rot)))%2**32
    return pack('<16I',*((v[i]+x[i])%2**32 for i in range(16)))
def desc(t,s):return 6*s*3**t*(4+4*t+s.bit_length())
if __name__=='__main__':
    c=Compiler().program();rng=Random(173)
    for key in [bytes(32),bytes(range(32))]+[rng.randbytes(32) for _ in range(8)]:
        o,t=run(c,key);assert o==reference(key)
        if key==bytes(32):assert o.hex()=='76b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7da41597c5157488d7724e03fb8d84a376a43b8f41518a11cc387b669b2ee6586'
    S=2*len(c.code)+1
    print('block',len(c.code),S,t,desc(5,S),desc(6,S),c.labels)

```


```python
from collections import Counter,defaultdict
from itertools import product
from random import Random
from router import reference,desc
ROLES=('A','J','C','AL','AR','CL','CR','K')
def graph(n):
    rows=[]
    def ranges(r):
        for j in range(1,n):
            rows.append(((r+'L',j),((r,j-1),)))
            if j>1: rows.append(((r+'L',j),((r+'L',j-1),)))
        for j in reversed(range(n-1)):
            rows.append(((r+'R',j),((r,j+1),)))
            if j<n-2: rows.append(((r+'R',j),((r+'R',j+1),)))
    def join(r):
        for j in range(n):
            child=('K',j) if r=='A' else ('T',0)
            x=('J',j) if r=='A' else ('K',j)
            for ok,d in [(j>0,'L'),(j+1<n,'R')]:
                if ok:rows.append((child,(x,(r+d,j))))
    ranges('A');join('A');ranges('C');join('C')
    count=Counter();result=[]
    for v,ps in rows:
        items=[]
        for p in ps:items.append((p,count[p]));count[p]+=1
        result.append((v,items))
    return result,count
def enc_seeks(n,rows):
    pos=n*8*768;clock=0
    def addr(v):return 768*(8*v[1]+ROLES.index(v[0]))
    for v,ps in rows:
        fields=sorted([addr(p)+256*(1+h) for p,h in ps]+([] if v[0]=='T' else [addr(v)]))
        if abs(pos-fields[-1])<abs(pos-fields[0]):fields.reverse()
        for d in fields:
            clock+=max(256,abs(d-pos))+256 # reset accumulator and terminal heads in parallel on every seek
            pos=d+256
    return clock
def route(n,a,j,k,idx):
    out=[]
    for role,i in [('A',a),('C',k)]:
        direction='L' if i<j else 'R';sgn=1 if i<j else -1
        prev=(role,i)
        for u in range(i+sgn,j+sgn,sgn):
            v=(role+direction,u);out.append(idx[v,(prev,)]);prev=v
        v=('K',j) if role=='A' else ('T',0)
        p=('J',j) if role=='A' else ('K',j)
        out.append(idx[v,(p,prev)])
    assert out==sorted(out)
    return out
def fixture(n):
    rng=Random(n);rows,count=graph(n);T=('T',0)
    keys={v:rng.randbytes(32) for v in [*count,T]}
    def G(k,h):return int.from_bytes(reference(k)[h*32:(h+1)*32],'little')
    words=[];idx={}
    for a,(v,ps) in enumerate(rows):
        idx[v,tuple(p for p,h in ps)]=a;b=int.from_bytes(keys[v],'little')
        for p,h in ps:b^=G(keys[p],h)
        words.append(b)
    for a,j,k in product(range(n),repeat=3):
        if a==j or k==j:continue
        t={v:keys[v] for v in [('A',a),('J',j),('C',k)]}
        for r in route(n,a,j,k,idx):
            v,ps=rows[r];b=words[r]
            for p,h in ps:b^=G(t[p],h)
            t[v]=b.to_bytes(32,'little')
        assert t[T]==keys[T]
    return n*(n-1)**2
if __name__=='__main__':
    N=4224;rows,counts=graph(N);assert Counter(counts.values())=={2:33776,1:12}
    assert len(rows)==50672
    E=enc_seeks(N,rows)
    print('row emission ticks',E,'valid route fixtures',sum(fixture(n) for n in range(2,7)))
    # Enc with padded source mask and raw fixed-field output.
    Tenc=33788*(51380+512+640)+4*768+E+1024+3*N*260+4096
    # Dec input is a single framed concatenation with triple, selected keys and packet.
    # Up to 8192 extra bus/temp repositioning and XOR/copy ticks per expansion.
    Tdec=2*(12972033+3*N*257+39)+16+(2*N+2)*(51380+16384)+65536
    # Envelope for unrolled outer translations, allowing two states per tick.
    Senc=2*Tenc+128;Sdec=2**40+N*(N-1)**2*(2*Tdec+128)
    print(Tenc,Tdec,Senc,Sdec,desc(6,Senc),desc(6,Sdec),Tenc+Tdec+desc(6,Senc)+desc(6,Sdec))

```


Save as selector.py and run for the smaller all-triple selector and finite state estimate.

```python
from itertools import product
from random import Random
from packet import graph,route,desc

def take(v,ps,a,j,c):
    role,t=v
    if role=='K' or role=='T':
        p,d=ps[1][0];other=a if role=='K' else c
        return d==j and ((p.endswith('L') and other<d) or (p.endswith('R') and other>d))
    i=a if role[0]=='A' else c
    direct=len(ps[0][0][0])==1
    if role[1]=='L':
        return j>=t and (i==t-1 if direct else i<t-1)
    return j<=t and (i==t+1 if direct else i>t+1)
for n in range(2,11):
    rows,_=graph(n);idx={(v,tuple(p for p,h in ps)):r for r,(v,ps) in enumerate(rows)}
    for a,j,c in product(range(n),repeat=3):
        if a==j or c==j:continue
        assert route(n,a,j,c,idx)==[r for r,(v,ps) in enumerate(rows) if take(v,ps,a,j,c)]
n=4224;rows,_=graph(n);idx={(v,tuple(p for p,h in ps)):r for r,(v,ps) in enumerate(rows)}
rng=Random(173)
for _ in range(24):
    a,j,c=rng.sample(range(n),3)
    assert route(n,a,j,c,idx)==[r for r,(v,ps) in enumerate(rows) if take(v,ps,a,j,c)]
m=12*n-16+3*n
T=605128904+512*m+65536
S=(m+1)*2**20
print(T,S,desc(6,S),2265773616+T+desc(6,4531547360)+desc(6,S))
```


Save as micro.py; this factors the identical 551-instruction quarter round and constructs its three-bit physical return addressing.

```python
from router import Compiler
def compressed():
    old=Compiler().program(); new=Compiler()
    beg=[i for i,(k,a,m) in enumerate(old.code) if k=='sumxor' and a==(0,1,3,True)][::2]
    assert len(beg)==8 and all(old.code[b:b+551]==old.code[beg[0]:beg[0]+551] for b in beg)
    loc={};i=0
    while i<len(old.code):
        loc[i]=len(new.code)
        if i in beg:
            q=beg.index(i)
            for j in range(3):
                new.op('putjump' if j==2 else 'put',(4,(q>>j)&1,'qr') if j==2 else (4,(q>>j)&1),{4:1})
            i+=551;new.mark('ret'+str(q))
        else:
            new.code.append(old.code[i]);i+=1
    new.op('jump',('done',));new.mark('qr');new.code+=old.code[beg[0]:beg[0]+551]
    new.op(moves={4:-1})
    for depth in range(3):
        for h in range(2**depth):
            new.mark('b%d_%d'%(depth,h))
            dest=tuple('ret'+str(2*h+j) if depth==2 else 'b%d_%d'%(depth+1,2*h+j) for j in (0,1))
            new.op('branch',dest,{4:-1} if depth<2 else {})
    new.mark('done')
    new.labels.update({k:loc[v] for k,v in old.labels.items()})
    return new
if __name__=='__main__':
 c=compressed();print(len(c.code),sum(k in ('sumxor','feed') and not a[-1] for k,a,m in c.code),c.labels)
```


Save as symbolic.py. Run with the path to Def_StreamedRouterBlock.lean to check both packed schedules against the independent word expressions for every input key.

```python
from router import Compiler
from itertools import product
from struct import unpack
from pathlib import Path
import re
class BoolDAG:
    def __init__(self):self.entries={}
    def node(self,op,*args):
        key=(op,*args)
        if key not in self.entries:self.entries[key]=len(self.entries)+258
        return self.entries[key]
    def xor(self,x,y):return self.node('xor',*sorted((x,y)))
    def add(self,x,y,c):return self.xor(self.xor(x,y),c),self.node('majority',*sorted((x,y,c)))
def symbolic(c,file,micro=False):
    # Check the exact run-length table stored by the Lean definition against the
    # assembled instructions, then symbolically replay that table. Booleans
    # 0,1 are constants; integers 2..257 are independent key variables.
    source=file.read_text()
    if micro:source=source.split('namespace SharedQuarterBlock',1)[1]
    src=source.split('def runs : Array (Nat × Nat) := #[',1)[1].split(']',1)[0]
    codes=[v for n,v in re.findall(r'\((\d+),(\d+)\)',src) for v in [int(v)]*int(n)]
    kinds=[];decoded=[]
    for word,(k,a,moves) in zip(codes,c.code,strict=True):
        if (k,a) not in kinds:kinds.append((k,a))
        m=tuple((0,1,-1)[(word//3**j)%3] for j in range(6))
        assert m==moves and kinds[word//729]==(k,a)
        decoded.append((k,a,m))
    dag=BoolDAG();tp=[{} for _ in range(5)]+[{i:i+2 for i in range(256)}]
    pc=0;heads=[0]*6;carry=0;out=[];ticks=0
    while pc<len(decoded):
        k,a,m=decoded[pc];pc+=1;m=list(m);ticks+=1
        def read(t):return tp[t].get(heads[t])
        def write(t,x):tp[t][heads[t]]=x
        if k=='put':write(*a)
        if k=='putjump':write(a[0],a[1]);pc=c.labels[a[2]]
        if k=='branch':
            v=read(4);assert v in (0,1);pc=c.labels[a[v]]
        if k=='copy':write(a[1],read(a[0]))
        if k=='sumxor':
            x,y,d,reset=a;b,carry=dag.add(read(x),read(y),0 if reset else carry)
            write(x,b);write(4,dag.xor(read(d),b))
        if k=='feed':
            x,q,reset=a;b,carry=dag.add(read(x),read(5) if q=='bus' else q,0 if reset else carry);out.append(b)
        if k=='jump':pc=c.labels[a[0]]
        if k=='find':
            v=read(4);assert v in (0,1,None)
            if v==0:pc=c.labels['find'];m[4]=-1
            elif v==1:write(4,0);pc=c.labels['back'];m[4]=1
            else:pc=c.labels['exit'];m[4]=1
        if k in ('back','exit'):
            v=read(4);assert v in (0,None)
            pc=c.labels[k if v==0 else ('again' if k=='back' else 'finish')];m[4]=1
        heads=[h+v for h,v in zip(heads,m)]
    def bits(x):return [(x>>i)&1 for i in range(32)]
    original=[bits(x) for x in unpack('<4I',b'expand 32-byte k')]+[list(range(2+32*j,34+32*j)) for j in range(8)]+[bits(0) for _ in range(4)]
    def addword(x,y):
        res=[];c=0
        for a,b in zip(x,y):
            d,c=dag.add(a,b,c);res.append(d)
        return res
    state=[v[:] for v in original]
    for r,j in product(range(20),range(4)):
        A,B,C,D=[4*k+(j+(r%2)*k)%4 for k in range(4)]
        for x,y,z,rot in ((A,B,D,16),(C,D,B,12),(A,B,D,8),(C,D,B,7)):
            state[x]=addword(state[x],state[y]);w=[dag.xor(a,b) for a,b in zip(state[z],state[x])]
            state[z]=w[-rot:]+w[:-rot]
    goal=[b for x,y in zip(state,original) for b in addword(x,y)]
    assert len(out)==512 and out==goal and heads==[0,0,0,0,0,256] and ticks==(51941 if micro else 51380)
    return len(dag.entries)
if __name__=='__main__':
 import sys
 from micro import compressed
 for c,m in [(Compiler().program(),False),(compressed(),True)]:
  print('structurally equal symbolic Boolean DAG outputs: 512;',symbolic(c,Path(sys.argv[1]),m),'internal nodes')
```

For a direct Lean machine smoke test, append this closed replay to a scratch copy of the definition file and run lake env lean on that copy. For the second machine substitute SharedQuarterBlock, 3206 and 51942 for StreamedRouterBlock, 7898 and 51381.

```lean
open StreamedRouterBlock
def delta : SignType → Int
 | .neg => -1
 | .zero => 0
 | .pos => 1
def leanReplay (key : Array Bool) : Array Bool × Nat := Id.run do
 let mut qs : Option (Fin 7898) := some 0
 let mut heads : Array Int := Array.replicate 5 0
 let mut wk : Array (Option Bool) := Array.replicate 700 none
 let mut output : Array Bool := #[]
 let mut pos : Int := 0
 let mut elapsed := 0
 for _ in [:51381] do
   let some st := qs | break
   elapsed := elapsed+1
   let rd := fun i : Fin 5 => wk[140*i.val+(heads[i.val]!+2).toNat]?.join
   let bit := if pos<0 then none else key[pos.toNat]?
   match machine.machine.tr st bit rd (fun j => Fin.elim0 j) false with
   | .query i _ => Fin.elim0 i
   | .step a _ _ =>
     for t in [:5] do
       let i : Fin 5 := ⟨t%5,by omega⟩
       let h := heads[t]!
       let (w,d) := a.workTapes i
       if let some sym := w then wk := wk.set! (140*t+(h+2).toNat) sym
       heads := heads.set! t (h+delta d)
     pos := pos+delta a.inputTape
     if let some o := a.output then output := output.push o
     qs := a.state
 return (output,elapsed)
def rfcExpected : Array Nat := #[118,184,224,173,160,241,61,144,64,93,106,229,83,134,189,40,189,210,25,184,160,141,237,26,168,54,239,204,139,119,13,199,218,65,89,124,81,87,72,141,119,36,224,63,184,216,74,55,106,67,184,244,21,24,161,28,195,135,182,105,178,238,101,134]
#eval let (o,t):= leanReplay (Array.replicate 256 false); (t,o.size,(Array.range 512).all fun i => o[i]? == some ((rfcExpected[i/8]?.getD 0).testBit (i%8)))
```

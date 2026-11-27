---
title: Rebuild and replay the complete two-join finite controls
refs: [note:pq-we-complete-chronological-router]
tags: [witness-encryption, reproducibility, turing-machines]
---

Save each listing under its indicated name in one directory. Run router-compact180.py, router-emit180.py, router-select180.py, router-build180.py, router-run180.py (also with the argument real), and router-packed180.py with Python 3. The latter decodes the same numerical format used by the Lean definition. To regenerate the definition run python3 router-export180.py Def_ChronologicalRouter.lean. The first three listings supply the independently described word function, physical quarter program, and graph.

### router.py

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

### micro.py

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

### packet.py

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

### router-compact180.py

```python
"""Compile a six-work-tape in-place single-block kernel, including private persistent ROM bootstrap."""
from collections import Counter
from pathlib import Path
from itertools import groupby
from struct import pack
from random import Random
import sys, json
from router import Compiler,reference,desc
from micro import compressed

# An instruction is (opcode, field arguments, head movements, next instruction);
# carry state for the PRE/POST stream is explicitly enumerated, old add instructions
# allocate the separate carry-consuming controls counted below.
class C:
 def __init__(self):self.cs=[];self.lab={}
 def label(self,l):assert l not in self.lab;self.lab[l]=len(self.cs)
 def op(self,op='',a=(),m=(),dst=None):
  d=list(m)+[0]*(6-len(m));self.cs.append((op,a,tuple(d),dst))
 def stream(self,stage,forwards,fn,ncarry):
  for word in range(4):
   for c in range(ncarry):
    self.label((stage,word,c))
    self.op('stream',(stage,word,c,forwards,fn))
def compile():
 c=C();o=compressed()
 # The ROM lies strictly left of cell zero on scratch. Bootstrap runs once.
 c.op(m=(0,0,0,0,-1))
 b=b'expand 32-byte k'
 for k in range(128):
  c.op('put',(4,(b[k//8]>>(k%8))&1),(0,0,0,0,-1))
  if k%32==31:c.op('put',(4,None),(0,0,0,0,-1))
 # Return to kernel origin using the same ROM scanning machinery (including end blanks).
 c.op(m=(0,0,0,0,1));c.op(m=(0,0,0,0,1),dst=('boot',0,0))
 c.stream('boot',False,'idle',1)
 c.label('entry');c.op(m=(0,0,0,0,-1),dst=('i1',0,0))
 c.stream('i1',True,'i1',1)
 c.stream('i2',False,'i2',1)
 c.stream('rew1',True,'rew1',1)
 c.stream('rew2',False,'rew2',1)
 c.label('tokens')
 for op,a,m in o.code[:12]:c.op(op,a,m)
 c.op(dst=('core',o.labels['pair']))
 # Original shared-body compiler has a physical appendix after feedforward.
 for i,(op,a,m) in enumerate(o.code):
  if not(o.labels['pair']<=i<o.labels['finish']+1 or o.labels['qr']<=i<len(o.code)):continue
  c.label(('core',i)); nxt='post' if i==o.labels['finish'] else ('core',i+1)
  if op in ('branch','jump','putjump'):
   if op=='branch':a=tuple(('core',o.labels[x]) for x in a)
   elif op=='jump':nxt=('core',o.labels[a[0]])
   else:a=a[:2];op='put';nxt=('core',o.labels[o.code[i][1][2]])
  c.op(op,a,m,nxt)
 c.label('post')
 for _ in range(13):c.op(m=(0,0,0,0,-1))
 c.op(dst=('f1',0,0))
 c.stream('f1',True,'f1',4)
 c.stream('f2',False,'f2',2)
 c.label('reset');c.op('reset')
 c.label('end')
 c.old=o
 return c
# Shared step implementation below depends only on the instruction and six observed symbols.
# It can be specialized over the finite read alphabet to generate the full dense table.
def step(c,pc,r,cin):
 op,a,m,dst=c.cs[pc];m=list(m);w={};co=0
 if op=='stream':
  stage,i,v,f,fn=a;d=-1 if f else 1
  if r[4] is None:
   if i<3:dst=(stage,i+1,0);m[4]=d
   else:
    target={'boot':'entry','i1':('i2',0,0),'i2':('rew1',0,0),'rew1':('rew2',0,0),'rew2':'tokens','f1':('f2',0,0),'f2':'reset'}[stage]
    dst=target
    if f:m[4]=1
    if stage=='i2':m[4]=-1
    if stage=='f2':m[2]=-1
  else:
   m[4]=d
   if fn=='i1': w={0:r[4],1:r[5],3:0};m[0]=m[1]=m[3]=m[5]=1
   if fn=='i2': w={2:r[5]};m[0]=m[1]=m[3]=-1;m[2]=m[5]=1
   if fn=='rew1':m[2]=m[5]=-1
   if fn=='rew2':m[5]=-1
   if fn=='f1':
    x=(r[0] or 0)+r[4]+v%2;y=(r[1] or 0)+(r[5] or 0)+v//2
    w={0:x%2,1:y%2};v=x//2+2*(y//2);m[0]=m[1]=m[5]=1
   if fn=='f2':
    y=(r[2] or 0)+(r[5] or 0)+v;w={2:y%2};v=y//2;m[0]=m[1]=-1;m[2]=m[5]=1
   dst=(stage,i,v if fn in ('f1','f2') else 0)
 if op=='reset':
  if r[2] is None:m[2]=1;dst='end'
  else:m[2]=-1;dst='reset'
 if op=='put':w={a[0]:a[1]}
 if op=='copy':w={a[1]:r[a[0]]}
 if op=='sumxor':
  j,k,z,reset=a;b=(r[j] or 0)+(r[k] or 0)+(0 if reset else cin);co=b//2;w={j:b%2,4:(r[z] or 0)^(b%2)}
 if op=='branch':dst=a[int(r[4] or 0)]
 if op in ('find','back','exit'):
  dest,shift=({'find':('exit',1)}[op] if op=='find' and r[4] is None else ('find',-1) if op=='find' and r[4]==0 else ('back',1) if op=='find' else (op if r[4]==0 else ('again' if op=='back' else 'finish'),1))
  if op=='find' and r[4]==1:w={4:0}
  dst=('core',c.old.labels[dest]);m[4]=shift
 return (pc+1 if dst is None else c.lab[dst]),w,m,co
def replay(c,k,setup=True,t=None):
 if t is None:t=[{} for _ in range(6)]
 for i in range(256):t[5][i]=(k[i//8]>>(i%8))&1
 p=[0]*6;pc=0 if setup else c.lab['entry'];carry=tt=0
 while pc<len(c.cs):
  r=[t[j].get(x) for j,x in enumerate(p)];pc,w,m,carry=step(c,pc,r,carry)
  for j,v in w.items():t[j][p[j]]=v
  p=[x+y for x,y in zip(p,m)];tt+=1
 assert p==[0,0,0,0,0,256],p
 bits=[t[j][i] for j in range(4) for i in range(128)]
 return bytes(sum(bits[8*i+j]<<j for j in range(8)) for i in range(64)),tt,t
def states(c):
 return 1+len(c.cs)+sum(op=='sumxor' and not a[-1] for op,a,*_ in c.cs)
if __name__=='__main__':
 c=compile();rng=Random(180);t=None
 for i,k in enumerate([bytes(32),bytes(range(32))]+[rng.randbytes(32) for _ in range(6)]):
  y,clk,t=replay(c,k,i==0,t); assert y==reference(k)
  if not i:setup=clk
 print('states',states(c),'ticks',clk,'one-time bootstrap',setup-clk,'pcs',len(c.cs),'ROM',c.lab['entry'])
 old=51380
 clock=2265773616+605128904+(clk-old)*(33788+8450)+2*(setup-clk)
 print('two clocks and tables',clock+2*desc(6,states(c)),'remaining',2**32-1-clock-2*desc(6,states(c)))

```

### router-emit180.py

```python
"""Construct a finite bit-level emitter for the entire row sweep on a delimiter tape."""
from itertools import groupby
from packet import graph,ROLES
def rowspec(n):
 pos=24*n;groups=[]
 for v,ps in graph(n)[0]:
  addr=lambda u:3*(8*u[1]+ROLES.index(u[0]))
  fld=sorted([addr(u)+h+1 for u,h in ps]+([] if v[0]=='T' else [addr(v)]))
  if abs(pos-fld[-1])<abs(pos-fld[0]):fld.reverse()
  cmd=[]
  for f in fld:
   cmd.append(('abs',f) if abs(f-pos)>80 else ('rel',f-pos));pos=f+1
  i=v[1] if v[0]!='T' else ps[0][0][1];groups.append((v[0],i,tuple(cmd)))
 g=[(r,tuple(x[2] for x in z)) for (r,i),z in groupby(groups,key=lambda x:x[:2])]
 return [(r,len(list(z)),cmd) for (r,cmd),z in groupby(g)]
class Emit:
 def __init__(self,n):
  self.c=[];self.labels={};self.model=rowspec(n)
  for gi,(r,count,rect) in enumerate(self.model):
   if count>1:
    # Decimal constant is an authoring convenience only. The binary register has explicit head operations.
    for i in range((count-1).bit_length()):self.op('counterInit',int((count-1)>>i&1))
    self.op('counterBack1');self.op('counterBack')
   self.labels['start',gi]=len(self.c)
   for row in rect:
    for j,(kind,d) in enumerate(row):
     if kind=='abs':
      self.op('left');self.op('homeScan');self.op('homeBlank');self.op('enter')
      assert d>=0
     if d<0:
      self.op('left');self.op('left')
      for i in range(-d):self.op('prev',i==-d-1)
     else:
      for _ in range(d):self.op('next')
     self.op('fold',(j==0,j+1==len(row),r=='T' and j+1==len(row)))
     self.op('rewind',(r=='T' and j+1==len(row)))
   if count>1:
    self.op('counterDec');self.op('counterRet',gi);self.op('counterDone')
 def op(self,k,a=None):self.c.append((k,a))
def step(e,p,r):
 op,a=e.c[p];q=p+1;m=[0]*6;w={};out=None
 if op=='left':m[5]=-1
 if op=='enter':m[5]=1
 if op=='next':m[5]=1;q=p if r[5] is not None else q
 if op=='prev':
  m[5]=1 if a and r[5] is None else -1;q=p if r[5] is not None else q
 if op=='homeScan':
  m[5]=-1;q=q if r[5] is None else p
 if op=='homeBlank':
  if r[5] is None:m[5]=1
  else:m[5]=-1;q=p-1
 if op=='fold':
  first,last,term=a
  if r[5] is None:m[5]=1;m[0]=-1;m[2]=-1 if term else 0
  else:
   x=(r[5] or 0)^((r[0] or 0) if not first else 0)^((r[2] or 0) if term else 0)
   w[0]=x;out=x if last else None;m[0]=m[5]=1;m[2]=1 if term else 0;q=p
 if op=='rewind':
  if r[0] is None:m[0]=1;m[2]=1 if a else 0
  else:m[0]=-1;m[2]=-1 if a else 0;q=p
 if op=='counterInit':w[1]=a;m[1]=1
 if op=='counterBack1':w[1]=None;m[1]=-1
 if op=='counterBack':m[1]=-1 if r[1] is not None else 1;q=p if r[1] is not None else q
 if op=='counterDec':
  if r[1] is None:q=p+2;m[1]=-1
  elif r[1]==0:w[1]=1;m[1]=1;q=p
  else:w[1]=0;m[1]=-1
 if op in ('counterRet','counterDone'):
  m[1]=-1 if r[1] is not None else 1
  if r[1] is not None:q=p
  elif op=='counterRet':q=e.labels['start',a]
 return q,w,m,out
def replay(n,L):
 e=Emit(n);mask=(1<<L)-1;fields=[((i*117)^((i*i+13)*97))&mask for i in range(24*n)]
 t=[{} for _ in range(6)];term=17&mask
 for i in range(L):t[2][i]=term>>i&1
 for i,x in enumerate(fields):
  for j in range(L):t[5][(L+1)*i+j]=(x>>j)&1
 h=[0]*5+[len(fields)*(L+1)];out=[];p=tt=0
 while p<len(e.c):
  v=[t[i].get(x) for i,x in enumerate(h)];p,w,m,o=step(e,p,v);tt+=1
  for i,x in w.items():t[i][h[i]]=x
  if o is not None:out.append(o)
  h=[x+d for x,d in zip(h,m)]
  assert tt<2_000_000
 ws=[]
 for v,ps in graph(n)[0]:
  addr=lambda u:3*(8*u[1]+ROLES.index(u[0]))
  z=term if v[0]=='T' else fields[addr(v)]
  for u,k in ps:z^=fields[addr(u)+1+k]
  ws.extend(z>>j&1 for j in range(L))
 assert out==ws,(n,L,len(out),len(ws))
 return tt
if __name__=='__main__':
 for n in range(3,17):
  for l in (1,5,16):replay(n,l)
 e=Emit(4224)
 print('issuer pcs',len(e.c),'sweep tests',42)

```

### router-select180.py

```python
"""Uniform, six-work-tape chronological selector. No random access to the packet or to the triple."""
from itertools import product
from packet import graph,route,ROLES
class P:
 def __init__(self):self.code=[];self.labels={}
 def label(self,z):assert z not in self.labels;self.labels[z]=len(self.code)
 def op(self,read=(),f=None,w=None,m=None,n=None,o=None,im=0):
  self.code.append((tuple(read),f if f else lambda r:(n,w or {},m or {},o,im)))
 def go(self,n):self.op(n=n)
def compile(n,width=None):
 b=width or (n-1).bit_length();s=P()
 # Work heads 0 and 1 are operand streams, 2 holds four trit answers, 3 the first-iteration flag.
 # All use the negative half of their work tapes with cell -1 reserved as a guard for the block.
 s.events={};L='bad';s.op(m={0:-1,1:-1,2:-1,3:-1});s.op(m={0:-1,1:-1,2:-1,3:-1})
 for k in range(3):
  for i in range(b):
   s.op((6,),lambda r:(None if r[6]==1 else L,{},{},None,1))
   s.op((6,),lambda r,k=k:(None if r[6] is not None else L,{0:r[6],**({3:r[6]} if k==1 else {})},{0:-1,**({3:-1} if k==1 else {})},None,1))
  s.op(m={0:-1})
 s.op((6,),lambda r:(None if r[6]==0 else L,{},{},None,1))
 # Read backwards first the C and then the A word against J. Ignore the physical J word in between.
 s.op(m={0:1,3:1});s.op(m={0:1})
 for k in ('C','J','A'):
  s.label(('neq',k,False))
  for differ in (False,True):
   if differ:s.label(('neq',k,True))
   def neq(r,k=k,d=differ):
    if r[0] is None:return (('endword',k) if d or k=='J' else L,{},{},None,0)
    if k=='J':return (('neq',k,False),{},{0:1},None,0)
    return (('neq',k,d or r[0]!=r[3]),{},{0:1,3:1},None,0)
   s.op((0,3),neq)
  s.label(('endword',k))
  if k=='C':
   s.op(m={0:1,3:-1});s.label('backJ')
   s.op((3,),lambda r:(None if r[3] is None else 'backJ',{},{3:1 if r[3] is None else -1},None,0))
  elif k=='J':s.op(m={0:1})
  else:s.op(m={0:-1,3:-1})
 # Tape 3 at -2 now; only first flag is used. Input head is parked at packet start.
 stages=('check','src','AL','AR','K','CL','CR','T')
 for index,st in enumerate(stages):
  s.label(('setup',st))
  direction=-1 if st in ('AR','CR') else 1
  start=n-2 if direction<0 else 1 if st in ('AL','CL') else 0
  end=0 if direction<0 else n-1
  off=-direction if st in ('AL','AR','CL','CR') else 0
  vals=[start+off,start,start+off,start]
  if st=='check':vals=[n-1]*4
  # Write tape1. Skip the old three words on tape0, then install its stopping coordinate.
  for z,x in enumerate(vals):
   for i in range(b):
    w={1:x>>i&1}
    if z==3:w[0]=end>>i&1
    s.op(w=w,m={0:-1,1:-1})
   s.op(m={0:-1,1:-1} if z<3 else {0:1,1:1})
  # After final bit both heads were at final delimiter and have stepped back one cell.
  def reverse_words(tag,heads):
   h=heads[0]
   for z in range(4):
    nm=(tag,'rev',z);s.label(nm)
    s.op((h,),lambda r,nm=nm,z=z,h=h,heads=heads:(nm if r[h] is not None else None,{},dict.fromkeys(heads,1 if r[h] is not None or z<3 else -1),None,0))
  reverse_words(('init',st),[0,1])
  s.op(w={3:1})
  s.label(('cmp',st))
  for z in range(4):
   for sign in (0,-1,1):
    nm=(st,'compare',z,sign);s.label(nm)
    def cmp(r,st=st,z=z,sign=sign):
     if r[0] is None:
      return ((st,'compare',z+1,0) if z<3 else ('rew',st),{2:{0:None,-1:0,1:1}[sign]},
             {0:-1 if z<3 else 1,1:-1 if z<3 else 1,2:-1 if z<3 else 1},None,0)
     d=r[0]-(r[1] or 0)
     return ((st,'compare',z,d or sign),{},{0:-1,1:-1},None,0)
    s.op((0,1),cmp)
  s.label(('rew',st))
  reverse_words(('cmp',st),[0,1])
  s.op(m={2:1});s.op(m={2:1}) # answer head was at -4; return to -2
  if st=='check':
   for i in range(3):s.op((2,),lambda r:(L if r[2]==1 else None,{},{2:-1},None,0))
   for i in range(3):s.op(m={2:1})
   s.go(('setup','src'));continue
  if st=='src':plans=[[(0,0)],[(1,0)],[(2,0)]]
  elif st in ('K','T'):
   x=0 if st=='K' else 2;plans=[[(1,0),(x,-1)],[(1,0),(x,1)]]
  else:
   x=0 if st.startswith('A') else 2
   plans=[[(x,0),(1,(0,1) if direction>0 else (-1,0))],[(x,-direction),(1,(0,1) if direction>0 else (-1,0))]]
  for j,pred in enumerate(plans):
   aft=(st,'after',j);done=(st,'store',j);fail=(st,'no',j)
   if ((st in ('K','T') and j==0) or (st in ('AL','AR','CL','CR') and j==1)):
    s.op((3,),lambda r,aft=aft:(aft if r[3]==1 else None,{},{},None,0))
   if st in ('K','T') and j==1:
    for k in range(3):s.op(m={2:-1})
    s.op((2,),lambda r,st=st,j=j:((st,'lastSkip',j) if r[2] is None else None,{},{},None,0))
    for k in range(3):s.op(m={2:1})
   for k,(slot,rule) in enumerate(pred):
    for h in range(slot):s.op(m={2:-1})
    signset=rule if isinstance(rule,tuple) else (rule,)
    vals={ {-1:0,0:None,1:1}[v] for v in signset}
    s.op((2,),lambda r,vals=vals,st=st,j=j,k=k:(None if r[2] in vals else (st,'failed',j,k),{},{},None,0))
    for h in range(slot):s.op(m={2:1})
   s.events[len(s.code)]=(st,j,True);s.op(o=1,n=aft)
   for k,(slot,rule) in enumerate(pred):
    s.label((st,'failed',j,k))
    for h in range(slot):s.op(m={2:1})
    s.events[len(s.code)]=(st,j,False);s.op(o=0,n=aft)
   if st in ('K','T') and j==1:
    s.label((st,'lastSkip',j))
    for k in range(3):s.op(m={2:1})
   s.label(aft)
  for k in range(3):s.op(m={2:-1})
  s.op((2,),lambda r,st=st:((st,'exit') if r[2] is None else None,{},{},None,0))
  for k in range(3):s.op(m={2:1})
  s.op(w={3:0})
  for z in range(4):
   for carry in (1,0):
    nm=(st,'advance',z,carry);s.label(nm)
    def inc(r,st=st,z=z,carry=carry,dr=direction):
     if r[1] is None:return ((st,'advance',z+1,1) if z<3 else (st,'advrew'),{},{1:-1 if z<3 else 1},None,0)
     new=r[1]^(carry!=0);nc=int(carry and r[1]==(1 if dr>0 else 0))
     return ((st,'advance',z,nc),{1:int(new)},{1:-1},None,0)
    s.op((1,),inc)
  s.label((st,'advrew'));reverse_words(('inc',st),[1]);s.go(('cmp',st))
  s.label((st,'exit'))
  for k in range(3):s.op(m={2:1})
  s.go(('setup',stages[index+1]) if index+1<len(stages) else 'halt')
 s.label(L);s.op(n='halt') # caller interprets early halt as rejecting request
 s.label('halt')
 return s
def run(s,n,a,j,c,b):
 data=[k for x in (a,j,c) for i in range(b) for k in (1,x>>i&1)]+[0]
 return raw(s,data)
def raw(s,data):
 t=[{} for _ in range(6)];h=[0]*6;out=[];p=ip=tt=0
 while p<len(s.code):
  r=[t[i].get(x) for i,x in enumerate(h)]+[data[ip] if 0<=ip<len(data) else None]
  q,w,m,o,im=s.code[p][1](r);p=p+1 if q is None else s.labels[q]
  for i,v in w.items():t[i][h[i]]=v
  for i,d in m.items():h[i]+=d
  if o is not None:out.append(o)
  ip+=im;tt+=1
  assert tt<80_000_000
 return out,tt
if __name__=='__main__':
 for n in range(2,7):
  b=(n-1).bit_length();s=compile(n)
  rows,_=graph(n);idx={(v,tuple(p for p,h in ps)):i for i,(v,ps) in enumerate(rows)}
  for a,j,c in product(range(1<<b),repeat=3):
   out,tt=run(s,n,a,j,c,b)
   if max(a,j,c)>=n or a==j or c==j:assert not out,(n,a,j,c,out[:5]);continue
   rr=set(route(n,a,j,c,idx));expected=[int(u==i) for i in range(n) for u in (a,j,c)]+[int(i in rr) for i in range(len(rows))]
   assert out==expected,(n,a,j,c,out,expected)
 print('selector pcs',len(compile(4224).code))

```

### router-build180.py

```python
"""Slot generator and wrapper bridges. The RNG is the registered fresh bit per tick."""
from importlib.machinery import SourceFileLoader as L
from pathlib import Path
d=Path(__file__).parent
sel=L('sel',str(d/'router-select180.py')).load_module()
core=L('core',str(d/'router-compact180.py')).load_module()
em=L('em',str(d/'router-emit180.py')).load_module()
def build(n,l=256):
 p=sel.P();jump=p.go;b=(n-1).bit_length()
 def move(i,d):p.op(m={i:d})
 # Mark l private timing cells on tape1 below -1.
 move(1,-1);move(1,-1)
 for _ in range(l):p.op(w={1:1},m={1:-1})
 move(1,1);p.label('timer-home');p.op((1,),lambda r:('timer-home' if r[1] is not None else None,{},{1:1},None,0))
 # First run the ROM bootstrap once. Its final state enters the wrapper, not the kernel.
 p.go('BOOT');p.label('boot-return')
 # Index counter on tape3; its -1 guard stays blank.
 move(3,-1);move(3,-1)
 for i in range(b):p.op(w={3:(n-1)>>i&1},m={3:-1})
 move(3,1);p.label('ih');p.op((3,),lambda r:('ih' if r[3] is not None else None,{},{3:1},None,0))
 p.label('index')
 move(2,-1);move(2,-1)
 for i in range(8):
  p.op(w={2:1},m={2:-1});p.op(w={2:int(i<3)},m={2:-1})
 move(2,1);p.label('rh');p.op((2,),lambda r:('rh' if r[2] is not None else None,{},{2:1},None,0))
 p.label('slot');move(2,-1);move(2,-1);p.label('seek-role')
 p.op((2,),lambda r:('index-over' if r[2] is None else 'skiprole' if r[2]==0 else None,{2:0} if r[2]==1 else {},{2:-1} if r[2] is not None else {},None,0))
 p.op((2,),lambda r:('flag' if r[2]==1 else 'home-no',{},{},None,0))
 p.label('skiprole');p.op(m={2:-1},n='seek-role')
 p.label('flag');p.op((6,),lambda r:(None if r[6]==1 else 'bad',{},{},None,1))
 p.op((6,),lambda r:('bad' if r[6] is None else 'home-on' if r[6]==1 else 'home-off',{},{},r[6],1))
 for z in ('on','off','no'):
  p.label('home-'+z);p.op((2,),lambda r,z=z:('home-'+z if r[2] is not None else None,{},{2:1,**({1:-1} if r[2] is None else {})},None,0))
  p.op(m={1:-1})
  p.label('bits-'+z)
  p.op((1,7),lambda r,z=z:('unseed' if r[1] is None else 'bits-'+z,{} if r[1] is None else {5:r[7]},
        {1:1} if r[1] is None else {1:-1,5:1},None if r[1] is None or z=='no' else r[7] if z=='on' else 0,0))
 p.label('unseed');p.op((1,),lambda r:('unseed' if r[1] is not None else 'CORE',{},{1:1,**({5:-1} if r[1] is not None else {})},None,0))
 p.label('core-return');move(5,1)
 for i in range(4):
  p.label(('dump',i))
  p.op((i,),lambda r,i=i:(('dump',i) if r[i] is not None else None,{} if r[i] is None else {5:r[i]},
             ({i:1,5:1,**({i-1:-1} if i else {})} if r[i] is not None else ({5:1} if i%2 else {})),None,0))
 p.op(m={3:-1});p.label('dump-home')
 p.op((3,),lambda r:('dump-home' if r[3] is not None else 'slot',{},{3:-1 if r[3] is not None else 1},None,0))
 p.label('index-over');move(2,1);p.label('role-home');p.op((2,),lambda r:('role-home' if r[2] is not None else None,{},{2:1},None,0))
 move(3,-1);move(3,-1);p.label('dec')
 p.op((3,),lambda r:(('finish-index' if r[3] is None else 'dec' if not r[3] else 'more-index'),{} if r[3] is None else {3:1-r[3]},{3:-1 if r[3]==0 else 1},None,0))
 for z,dst in [('more-index','index'),('finish-index','terminal')]:
  p.label(z);p.op((3,),lambda r,z=z,dst=dst:(z if r[3] is not None else dst,{},{3:1},None,0))
 p.label('terminal')
 # frame boundary for mask; then tag and value for the message.
 p.op((6,),lambda r:(None if r[6]==0 else 'bad',{},{},None,1))
 p.op((6,),lambda r:(None if r[6]==1 else 'bad',{},{},None,1))
 move(1,-1);move(1,-1);p.label('terminal-bits')
 p.op((1,7),lambda r:('terminal-bits' if r[1] is not None else None,{} if r[1] is None else {2:r[7]},
       {1:-1,2:1} if r[1] is not None else {1:1},None,0))
 p.label('terminal-home');p.op((1,),lambda r:('terminal-home' if r[1] is not None else None,{},{1:1,**({2:-1} if r[1] is not None else {})},None,0))
 # Scratch row 1 holds stale block words. Clear the positive sweep counter's far guard.
 for i in range((n-1).bit_length()):move(1,1)
 p.op(w={1:None})
 for i in range((n-1).bit_length()):move(1,-1)
 p.go('EMIT');p.label('sweep-return')
 p.op((6,2),lambda r:(None if r[6] is not None else 'bad',{},{},None,0))
 p.op((6,2),lambda r:(None,{},{},(r[6] or 0)^(r[2] or 0),1))
 p.label('bad');p.label('halt')
 return p
def check(n,l):
 p=build(n,l);e=em.Emit(n);labels=p.labels
 for a in ('BOOT','CORE','EMIT'):labels[a]=-1
 # Keys and local block pads at reduced widths for complete end-to-end issuer chronologies.
 # This test uses a deterministic toy block at the interface, so it checks orchestration separately.
 from random import Random
 from packet import graph,ROLES
 rng=Random(180+l);flags=[rng.randrange(2) for _ in range(3*n)];msg=1
 data=[u for x in flags for u in (1,x)]+[0,1,msg,0]
 t=[{} for _ in range(6)];h=[0]*6;out=[];ip=pc=0;fields=[];calls=0
 while pc<len(p.code):
  r=[t[i].get(x) for i,x in enumerate(h)]+[data[ip] if ip<len(data) else None,rng.randrange(2)]
  q,w,m,o,im=p.code[pc][1](r);pc=pc+1 if q is None else labels[q]
  for i,d in w.items():t[i][h[i]]=d
  for i,d in m.items():h[i]+=d
  if o is not None:out.append(o)
  ip+=im
  if q=='BOOT':assert h==[0]*6;pc=labels['boot-return']
  if q=='CORE':
   assert h[:5]==[0]*5
   key=sum(t[5][h[5]+i]<<i for i in range(l));h[5]+=l;v=key*((1<<l)+3)+5
   mask=(1<<l)-1;fields.extend([key,v&mask,(v>>l)&mask])
   for j in range(4):
    for i in range(l//2):t[j][i]=v>>(j*(l//2)+i)&1
   calls+=1;pc=labels['core-return']
  if q=='EMIT':
   assert h==[0]*5+[24*n*(l+1)],h
   term=sum(t[2][i]<<i for i in range(l));x=0
   while x<len(e.c):
    v=[t[i].get(j) for i,j in enumerate(h)];x,ww,mm,oo=em.step(e,x,v)
    for i,v in ww.items():t[i][h[i]]=v
    for i,v in enumerate(mm):h[i]+=v
    if oo is not None:out.append(oo)
   pc=labels['sweep-return']
 expected=[]
 for j in range(n):
  for a in range(3):
   z=flags[3*j+a];expected+=[z]+[(fields[24*j+3*a]>>i&1)*z for i in range(l)]
 for v,ps in graph(n)[0]:
  get=lambda u:3*(8*u[1]+ROLES.index(u[0]))
  z=term if v[0]=='T' else fields[get(v)]
  for u,d in ps:z^=fields[get(u)+1+d]
  expected+=[z>>i&1 for i in range(l)]
 expected+=[(term&1)^msg]
 assert expected==out and calls==8*n,(n,l,len(out),len(expected))
if __name__=='__main__':
 for n in (5,8,13):
  for l in (4,16,32):check(n,l)
 print('issuer wrapper states',len(build(4224).code))

```

### router-dec180.py

```python
"""Decoder superprogram. Every key/row operation is a finite transition on six work tapes."""
from importlib.machinery import SourceFileLoader as L
from pathlib import Path
d=Path(__file__).parent
smod=L('smod',str(d/'router-select180.py')).load_module()
def build(n,l=256):
 p=smod.P();m=lambda i,x:p.op(m={i:x})
 s=smod.compile(n);events=sorted(set((st,j) for st,j,_ in s.events.values()));ret={r:i for i,r in enumerate(events)}
 # Bootstrap three zeroed, guarded key slots; only one 256-state straight-line generator.
 # Two tokens on row 1 temporarily count the first two more-slots iterations.
 p.op(w={1:1},m={1:1});p.op(w={1:1},m={1:1});m(1,-1)
 p.label('newslot')
 for _ in range(l):p.op(w={5:0},m={5:1})
 p.op((1,),lambda r:('newslot' if r[1] is not None else None,{},{1:-1 if r[1] is not None else 1,5:1 if r[1] is not None else 0},None,0))
 def home(tag):
  # From any position in a nonempty field or immediately after it. A preceding blank guard pair marks home.
  p.label((tag,'scan'));p.op((5,),lambda r,tag=tag:((tag,'check') if r[5] is None else (tag,'scan'),{},{5:-1},None,0))
  p.label((tag,'check'));p.op((5,),lambda r,tag=tag:(None if r[5] is None else (tag,'scan'),{},{5:1 if r[5] is None else -1},None,0));m(5,1)
 def seek(slot):
  for i in range(slot):
   label=('seek',len(p.code));p.label(label)
   p.op((5,),lambda r,l=label:(l if r[5] is not None else None,{},{5:1},None,0))
 home('start');p.go('BOOT');p.label('boot-return');p.go(('sel',0))
 # Import selector, splice every write into a dispatch. All such writes occur with four heads at -2.
 for i,(rr,f) in enumerate(s.code):
  p.label(('sel',i))
  if i in s.events:
   st,j,yes=s.events[i];p.go(('event',st,j,yes));continue
  def wrap(r,f=f,i=i):
   q,w,mv,o,im=f(r)
   if q=='bad' or i==s.labels['bad']:nxt='bad'
   elif q=='halt':nxt='terminal'
   else:nxt=('sel',s.labels[q] if q is not None else i+1)
   return nxt,w,mv,o,im
  p.op(rr,wrap)
 p.label(('sel',len(s.code)));p.go('bad')
 def putbits(t,num,width,origin,offset):
  for _ in range(offset-origin):m(t,-1)
  for i in range(width):p.op(w={t:num>>i&1},m={t:-1})
  for _ in range(width+offset-origin):m(t,1)
 def readbits(t,width,origin,offset,key,targets):
  for _ in range(offset-origin):m(t,-1)
  for bit in range(width):
   for lo in range(1<<bit):
    p.label((key,bit,lo))
    p.op((t,),lambda r,t=t,i=bit,lo=lo,key=key:((key,i+1,lo+((r[t] or 0)<<i)),{},{t:-1 if i+1<width else 1},None,0))
  for k in range(1<<width):
   p.label((key,width,k))
   for _ in range(offset-origin+width-2):m(t,1)
   p.go(targets.get(k,'bad'))
 # On check-return from complete field, heads 0..3 must all be -2.
 for st,j in events:
  for yes in (False,True):
   p.label(('event',st,j,yes))
   putbits(3,ret[st,j],4,2,3)
   if st=='src':act=('opening',j,yes);p.go(act);continue
   if not yes:p.go('skip');continue
   if st in ('AL','CL'):p.go(('unary',st[0],0));continue
   if st in ('AR','CR'):
    if j==0:p.op((3,),lambda r,st=st:(('unary',st[0],0 if r[3] else 1),{},{},None,0))
    else:p.go(('unary',st[0],0))
    continue
   # The role half of the join's range changes at both boundaries; J uses half one for interior right only.
   role='A' if st=='K' else 'C'
   p.op((3,),lambda r,role=role:(('join',role,0,0) if r[3] else None,{},{},None,0))
   for _ in range(3):m(2,-1)
   p.op((2,),lambda r,role=role,j=j:(('edge-restore',role,j) if r[2] is None else ('inner-restore',role,j),{},{},None,0))
 for role in ('A','C'):
  for j in (0,1):
   for label,pad in [('edge-restore',(0,0)),('inner-restore',(j,1))]:
    p.label((label,role,j))
    for _ in range(3):m(2,1)
    p.go(('join',role,*pad))
 def tag():p.op((6,),lambda r:(None if r[6]==1 else 'bad',{},{},None,1))
 for j in range(3):
  for yes in (False,True):
   p.label(('opening',j,yes));tag()
   p.op((6,),lambda r,yes=yes:(None if r[6] is not None and (not yes or r[6]) else 'bad',{},{},None,1))
   if yes:seek(j)
   p.go('copy' if yes else 'skip')
 for name in ('copy','skip'):
  p.label(name)
  p.op((5,6),lambda r,nm=name:('back-field' if r[5] is None else None if r[6]==1 else 'bad',{},{},None,int(r[5] is not None)))
  p.op((6,),lambda r,nm=name:(nm if r[6] is not None else 'bad',{5:r[6]} if nm=='copy' else {},{5:1},None,1))
 p.label('back-field');home('field');p.go('dispatch')
 # Kernel calls begin at slot start with all four heads zero; three answer bits survive on tape2.
 # IDs encode the pad copy or body-combine continuation and its destination.
 contlist=[]
 def call(slot,cont):
  if cont not in contlist:contlist.append(cont)
  putbits(2,contlist.index(cont),4,2,6)
  for _ in range(2):p.op(m={j:1 for j in range(4)})
  seek(slot);p.go('CORE')
 for role,slot in [('A',0),('C',2)]:
  for half in (0,1):
   p.label(('unary',role,half));call(slot,('consume',slot,half,False))
  for hj,hr in ((0,0),(0,1),(1,1)):
   p.label(('join',role,hj,hr));call(1,('save',slot,hj,hr))
 p.label('core-return');home('core')
 for _ in range(2):p.op(m={j:-1 for j in range(4)})
 readbits(2,4,2,6,'inner-jump',{i:('cont',v) for i,v in enumerate(contlist)})
 # Install second-call continuations first. 'consume' replaces slot by selected half XOR body,
 # optionally XOR its old value Jpad. 'save' replaces J with its half before the second expansion.
 def rowop(half,mode):
  for row in (2*half,2*half+1):
   # All row heads are at -2; temporarily approach cell 0.
   m(row,1);m(row,1);lab=('row',len(p.code));p.label(lab)
   if mode=='save':
    p.op((row,),lambda r,row=row,lab=lab:(None if r[row] is None else lab,{} if r[row] is None else {5:r[row]},{row:-1} if r[row] is None else {row:1,5:1},None,0))
   else:
    p.op((row,6),lambda r,row=row,lab=lab:((lab,'rew') if r[row] is None else None if r[6]==1 else 'bad',{},{row:-1} if r[row] is None else {},None,int(r[row] is not None)))
    p.op((row,5,6),lambda r,row=row,lab=lab,mode=mode:(lab if r[6] is not None else 'bad',{5:(r[row] or 0)^(r[6] or 0)^((r[5] or 0) if mode=='join' else 0)},{row:1,5:1},None,1))
   p.label((lab,'rew'))
   p.op((row,),lambda r,row=row,lab=lab:((lab,'rew') if r[row] is not None else None,{},{row:-1},None,0))
 for slot in (0,2):
  for hj,hr in ((0,0),(0,1),(1,1)):
   p.label(('cont',('save',slot,hj,hr)));seek(1);rowop(hj,'save');home(('saved',slot,hj,hr))
   call(slot,('consume',1,hr,True))
 # The final additional continuations share the same physical ID tree; patch those leaves.
 for i,v in enumerate(contlist):
  start=p.labels['inner-jump',4,i]
  # readbits emits a fixed rewind then the sole unconditional jump.
  pos=start+(6-2+4-2)
  p.code[pos]=((),lambda r,v=v:(('cont',v),{},{},None,0))
 for slot in (0,2,1):
  for h in (0,1):
   p.label(('cont',('consume',slot,h,slot==1)));seek(slot);rowop(h,'join' if slot==1 else 'unary');home(('consumed',slot,h));p.go('dispatch')
 p.label('dispatch')
 readbits(3,4,2,3,'dispatch-jump',{i:('sel',s.labels[st,'after',j]) for (st,j),i in ret.items()})
 p.label('terminal');tag();seek(1)
 p.op((5,6),lambda r:(None if r[6] is not None else 'bad',{},{},(r[5] or 0)^(r[6] or 0),1));p.go('halt')
 p.label('bad');p.op(o=0,n='halt');p.label('halt')
 return p
if __name__=='__main__':print('decoder program pcs',len(build(4224).code))

```

### router-run180.py

```python
from pathlib import Path
from importlib.machinery import SourceFileLoader as L
from random import Random
from itertools import product
d=Path(__file__).parent
B=L('B',str(d/'router-build180.py')).load_module();D=L('D',str(d/'router-dec180.py')).load_module();co=B.core;em=B.em
def execute(p,n,l,data,mode,real=False):
 t=[{} for _ in range(6)];h=[0]*6;pc=ip=ticks=0;out=[];rng=Random(n+l);c=co.compile();e=em.Emit(n);clk={}
 while pc<len(p.code):
  rr,act=p.code[pc];r=[t[i].get(x) for i,x in enumerate(h)]+[data[ip] if 0<=ip<len(data) else None,rng.getrandbits(1)]
  ticks+=1;dst,w,m,o,im=act(r)
  for i,v in w.items():t[i][h[i]]=v
  for i,v in m.items():h[i]+=v
  if o is not None:out.append(o)
  ip+=im
  if dst in ('BOOT','CORE'):
   assert h[:5]==[0]*5,(mode,dst,h)
   if real:
    k=0 if dst=='BOOT' else c.lab['entry'];end=c.lab['entry'] if dst=='BOOT' else len(c.cs);carry=0
    while k!=end:
     r=[t[i].get(j) for i,j in enumerate(h)];k,w,m,carry=co.step(c,k,r,carry);ticks+=1
     for i,v in w.items():t[i][h[i]]=v
     for i,v in enumerate(m):h[i]+=v
   elif dst=='CORE':
    x=sum(t[5][h[5]+i]<<i for i in range(l));v=x*((1<<l)+3)+5
    for j in range(4):
     for i in range(l//2):t[j][i]=v>>(j*(l//2)+i)&1
    h[5]+=l
   dst='boot-return' if dst=='BOOT' else 'core-return'
  if dst=='EMIT':
   k=0
   while k<len(e.c):
    r=[t[i].get(j) for i,j in enumerate(h)];k,w,m,o=em.step(e,k,r);ticks+=1
    for i,v in w.items():t[i][h[i]]=v
    for i,v in enumerate(m):h[i]+=v
    if o is not None:out.append(o)
   dst='sweep-return'
  pc=pc+1 if dst is None else p.labels[dst]
  assert ticks<50_000_000,(mode,h,pc)
 return out,ticks
def frame(x):return [v for u in x for v in (1,u)]+[0]
def fixture(n,l,real=False):
 E=B.build(n,l);D0=D.build(n,l);w=(n-1).bit_length()
 tests=0;full=[]
 for flags,beta in [([1]*(3*n),1),([int((i*5+7)%7<4) for i in range(3*n)],1)]:
  ct,et=execute(E,n,l,frame(flags)+frame([beta]),'enc',real)
  triples=[(0,n-1,0),(n-1,0,n-1)] if real else product(range(1<<w),repeat=3)
  for a,j,c in triples:
   bits=[u>>i&1 for u in (a,j,c) for i in range(w)]
   v,dt=execute(D0,n,l,frame(bits)+frame(ct),'dec',real)
   ok=max(a,j,c)<n and a!=j and c!=j and flags[3*a] and flags[3*j+1] and flags[3*c+2]
   assert v==[beta if ok else 0],(a,j,c,v,beta,ok)
   tests+=1;full.append((et,dt))
 return tests,full
if __name__=='__main__':
 import sys
 real='real' in sys.argv
 for n in ((3,) if real else (2,3,4,5)):
  count,clocks=fixture(n,256 if real else 4,real);print(n,count,max(clocks),flush=True)

```

### router-export180.py

```python
"""Specialize each instruction on exactly its read symbols to build normative six-tape machines."""
import sys
from itertools import product
from pathlib import Path
from importlib.machinery import SourceFileLoader as L
d=Path(__file__).parent
B=L('B',str(d/'router-build180.py')).load_module();D=L('D',str(d/'router-dec180.py')).load_module()
co=B.core;em=B.em
def combined(n,typ):
 p=B.build(n) if typ=='enc' else D.build(n);core=co.compile();e=em.Emit(n)
 sp=len(p.code);carry=[i for i,(op,a,*_) in enumerate(core.cs) if op=='sumxor' and not a[-1]]
 nc=co.states(core);base=sp+nc
 ids={v:sp+len(core.cs)+i for i,v in enumerate(carry)}
 se=base+(len(e.c) if typ=='enc' else 0)
 def jump(x):
  if x=='CORE':return sp+core.lab['entry']
  if x=='BOOT':return sp
  if x=='EMIT':return base
  return p.labels[x] if p.labels[x]<sp else None
 def prog(k):
  reads,f=p.code[k]
  def f1(r):
   q,w,m,o,im=f(r);return (jump(q) if q is not None else k+1 if k+1<sp else None),w,m,o,im
  return reads,f1
 def block(i,cin):
  op,a,*_=core.cs[i]
  deps={'put':[],'copy':[a[0]] if op=='copy' else [],'branch':[4],'find':[4],'back':[4],'exit':[4],'reset':[2],'sumxor':list(a[:3]) if op=='sumxor' else []}
  if op=='stream':deps[op]=[4]+{'i1':[5],'i2':[5],'f1':[0,1,5],'f2':[2,5]}.get(a[-1],[])
  def g(r):
   q,w,m,cy=co.step(core,i,r,cin)
   if q==len(core.cs):dest=p.labels['core-return']
   elif i<core.lab['entry'] and q==core.lab['entry']:dest=p.labels['boot-return']
   else:dest=ids.get(q,sp+q) if cy else sp+q
   return dest,w,{j:m[j] for j in range(6)},None,0
  return tuple(deps.get(op,[])),g
 def emitter(i):
  op,a=e.c[i]
  deps={'next':(5,),'prev':(5,),'homeScan':(5,),'homeBlank':(5,),'fold':(0,2,5),'rewind':(0,), 'counterBack':(1,),'counterDec':(1,),'counterRet':(1,),'counterDone':(1,)}
  def g(r):
   q,w,m,o=em.step(e,i,r);return (base+q if q<len(e.c) else p.labels['sweep-return']),w,dict(enumerate(m)),o,0
  return deps.get(op,()),g
 ops=[prog(i) for i in range(sp)]+[block(i,0) for i in range(len(core.cs))]+[block(i,1) for i in carry]+[((),lambda r:(None,{},{},None,0))]
 if typ=='enc':ops+=[emitter(i) for i in range(len(e.c))]
 assert len(ops)==se
 return ops
def packbuild(ops):
 # A table triple consists of the relevant symbol mask, an offset, and a packed action per observation.
 # Delta-coded destinations and relative default targets share the same instruction word across PCs.
 tab={};actions=[];desc=[]
 for pc,(deps,f) in enumerate(ops):
  deps=sorted(set(deps));mask=sum(1<<i for i in deps);R=[]
  alph=lambda i:(0,1) if i==7 else (None,0,1)
  for v in product(*(alph(i) for i in reversed(deps))):
   r=[None]*7+[0]
   for i,x in zip(reversed(deps),v):r[i]=x
   q,w,m,o,im=f(r);delta=0 if q is None else q-pc
   a=0 if q is None else (1+2*delta if delta>=0 else -2*delta)
   a=a*3+(0 if o is None else 1+int(o))
   a=a*3+{0:0,1:1,-1:2}[im]
   for j in reversed(range(6)):
    wr=0 if j not in w else 1 if w[j] is None else 2+int(w[j])
    a=a*12+wr+4*{0:0,1:1,-1:2}[m.get(j,0)]
   R.append(a)
  key=tuple(R)
  if key not in tab:tab[key]=len(actions);actions+=R
  desc.append(mask+256*tab[key])
 return actions,desc
if __name__=='__main__':
 target=Path(sys.argv[1]);m='''import SigabaNeo.Trusted.Machine
namespace ChronologicalRouter
open SigabaNeo
def numbers (s : String) : Array Nat := (s.splitOn ",").toArray.map String.toNat!
def dir (n : Nat) : SignType := if n=1 then 1 else if n=2 then -1 else 0
def tern (x : Option Bool) : Nat := match x with | none => 0 | some b => 1+b.toNat
def key (mask : Nat) (rd : Nat → Nat) : Nat :=
  (List.range 8).reverse.foldl (fun n i =>
    if mask.testBit i then n * (if i=7 then 2 else 3) + rd i else n) 0
def get (s : Nat) : Option Bool := if s=0 then none else some (s=2)
def mk (states clock : Nat) (hp : 0<states) (actions desc : Array Nat) : Machine where
  tapes := 6
  states := states
  time := clock
  machine := {
    initial := ⟨0,hp⟩
    tr := fun q input ws _ coin =>
      let d := desc[q.val]?.getD 0
      let rd := fun i : Nat => if h : i<6 then tern (ws ⟨i,h⟩) else if i=6 then tern input else coin.toNat
      let a := actions[d/256 + key (d%256) rd]?.getD 0
      let top := a/12^6
      let z := top/9
      let dest := if z%2=1 then q.val + z/2 else q.val-z/2
      .step { inputTape := dir (top%3)
              workTapes := fun i =>
                let c := (a/12^i.val)%12
                let w := c%4
                (if w=0 then none else some (get (w-1)), dir (c/4))
              output := get ((top/3)%3)
              state := if z=0 then none else if h : dest<states then some ⟨dest,h⟩ else none }
            (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) }
'''
 for typ,clock in [('enc',2300047211),('dec',653426970)]:
  ops=combined(4224,typ);a,v=packbuild(ops);print(typ,len(ops),len(a),len(v),flush=True)
  for label,items in [('Actions',a),('Descriptors',v)]:
   m+='def '+typ+label+' : Array Nat := numbers "'+','.join(map(str,items))+'"\n'
  m+=f'def {typ} : Machine := mk {len(ops)} {clock} (by decide) {typ}Actions {typ}Descriptors\n'
 target.write_text(m+'end ChronologicalRouter\n')

```

### router-packed180.py

```python
"""Direct interpreter of the Lean descriptor, mixed-radix lookup and packed action."""
from pathlib import Path
from importlib.machinery import SourceFileLoader as L
from random import Random
import sys
d=Path(__file__).parent
x=L('xp',str(d/'router-export180.py')).load_module()
def run(tab,data,seed):
 a,v=tab;rng=Random(seed);h=[0]*6;t=[{} for _ in h];pc=ip=clock=0;out=[]
 while pc is not None:
  des=v[pc];mask=des%256;idx=0;coin=rng.getrandbits(1)
  for i in reversed(range(8)):
   if mask>>i&1:
    s=coin if i==7 else data[ip] if i==6 and 0<=ip<len(data) else None if i==6 else t[i].get(h[i])
    idx=idx*(2 if i==7 else 3)+(s if i==7 else 0 if s is None else 1+s)
  act=a[des//256+idx]
  for i in range(6):
   act,k=divmod(act,12);m,w=divmod(k,4)
   if w:t[i][h[i]]=None if w==1 else w-2
   h[i]+=(0,1,-1)[m]
  act,j=divmod(act,3);ip+=(0,1,-1)[j];z,o=divmod(act,3)
  if o:out.append(o-1)
  pc=None if z==0 else pc+(z//2 if z%2 else -(z//2))
  clock+=1
  assert clock<10_000_000
 return out,clock
def frame(x):return [v for u in x for v in (1,u)]+[0]
if __name__=='__main__':
 n=3
 enc,dec=[x.packbuild(x.combined(n,k)) for k in ('enc','dec')]
 ct,a=run(enc,frame([1]*9)+frame([1]),180)
 for trip in [(0,2,0),(2,0,1),(1,1,2),(3,0,1)]:
  prefix=[x>>i&1 for x in trip for i in range(2)]
  out,b=run(dec,frame(prefix)+frame(ct),181)
  assert out==[int(max(trip)<3 and trip[0]!=trip[1] and trip[2]!=trip[1])]
  print(trip,out,a,b,flush=True)

```

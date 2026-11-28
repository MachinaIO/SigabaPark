---
title: Reproduce NAND demand traces on actual native transition tables
refs: [definition:NandDemandRoles, note:nand-demand-native]
tags: [witness-encryption, reproducibility]
---

Save the following listings under the indicated names in one directory. Run python3 fixtures.py for the full physical words and oracle witnesses. Run python3 supplier.py for the independent greedy/guided falsification experiments. With the new DAG definition available, run lake env lean --run Table.lean and compile Replay.cpp with c++ -std=c++17 -O3. Run its executable with /tmp/demand204.tab followed by the chosen .bin input paths. The final 128 printed bits are input demands interpreted as an assignment; read them as a recovered witness only on a successful path. The zero ciphertext can also encode a successful zero message. Use lake env lean --run CoreWord.lean with a generated .gates source and target file; optional third argument 0 or 1 selects a one or zero encryption message respectively. Compare this file bytewise with the Python input. Native.lean offers a slower direct transition replay with no table extraction.

### supplier.py

```python
"""Two sweeps for a sufficient accepting witness, with registered gate semantics."""
from itertools import product
from random import Random

def evaluate(n, gates, witness):
    values = [True] + [bool((witness >> j)&1) for j in range(n)]
    for a,b in gates:
        end = len(values)
        values.append(not ((values[a] if a<end else True) and (values[b] if b<end else True)))
    return values[-1] if gates else True

def supplier(n,gates, select=None):
    if not gates:
        return 0
    # Bit 0 means false is feasible; bit 1 means true is feasible.
    possible = [2]+[3]*n
    parents = []
    for a,b in gates:
        end = len(possible)
        a,b = (a if a<end else 0), (b if b<end else 0)
        parents.append((a,b))
        x,y = possible[a],possible[b]
        possible.append(int(bool(x&y&2)) + 2*int(bool((x|y)&1)))
    if not (possible[-1]&2):
        return None
    demand = [0]*len(possible)
    demand[-1] = 2
    for i in reversed(range(len(parents))):
        a,b = parents[i]
        d = demand[n+i+1]
        if d==0:
            continue
        if d==3:
            return None
        if d==1:
            demand[a] |= 2
            demand[b] |= 2
        else:
            # Prefer a previously required false operand before a new request.
            c = next((v for v in (a,b) if demand[v]==1),None)
            if c is None:
                c = next((v for v in (a,b) if demand[v]==0 and possible[v]==1),None)
            if c is None:
                options = list(dict.fromkeys(v for v in (a,b) if demand[v]==0 and possible[v]&1))
                c = (options[select(i,a,b) if select and len(options)==2 else 0]
                     if options else None)
            if c is None: return None
            demand[c] |= 1
    if any(d==3 or d and not d&p for d,p in zip(demand,possible)):
        return None
    return sum((d==2)<<i for i,d in enumerate(demand[1:n+1]))

def planted(n,word,total):
    gates=[]
    def nand(a,b):
        gates.append((a,b))
        return n+len(gates)
    def neg(a): return nand(a,a)
    def conj(a,b): return neg(nand(a,b))
    def disj(a,b): return nand(neg(a),neg(b))
    terms=[]
    for i in range(n):
        x=i+1
        lit=x if word>>i&1 else neg(x)
        # This false branch makes all inputs syntactically mixed at the root.
        terms.append(disj(lit,conj(x,neg(x))))
    while len(terms)>1:
        terms=[conj(terms[j],terms[j+1]) if j+1<len(terms) else terms[j]
               for j in range(0,len(terms),2)]
    old=gates.pop()
    gates.extend([(0,0)]*(total-len(gates)-1))
    gates.append(old)
    return gates

def signs(n,gates):
    vals=[(0,0)]+[(1<<i,0) for i in range(n)]
    for a,b in gates:
        p,q=vals[a]
        r,s=vals[b]
        vals.append((q|s,p|r))
    return vals[-1]

def check():
    rand=Random(157)
    for n in range(1,7):
        for _ in range(250):
            g=[(rand.randrange(n+14),rand.randrange(n+14)) for _ in range(12)]
            w=supplier(n,g)
            assert w is None or evaluate(n,g,w)
            for word in range(1<<n):
                vals=[True]+[bool(word>>i&1) for i in range(n)]
                for a,b in g:
                    d=len(vals)
                    vals.append(not ((vals[a] if a<d else True) and (vals[b] if b<d else True)))
                if vals[-1]:
                    tape=[]
                    def guide(i,a,b):
                        choice=int(vals[a])
                        tape.append(choice)
                        return choice
                    representative=supplier(n,g,guide)
                    assert representative is not None and evaluate(n,g,representative)
                    it=iter(tape)
                    assert supplier(n,g,lambda *_:next(it))==representative
    for word in range(64):
        g=planted(6,word,100)
        assert [w for w in range(64) if evaluate(6,g,w)]==[word]
        assert supplier(6,g)==word
    for _ in range(40):
        word=rand.getrandbits(128)
        g=planted(128,word,4096)
        assert supplier(128,g)==word and evaluate(128,g,word)
        p,q=signs(128,g)
        assert (p&q).bit_count()==128
    print('1500 unrestricted small DAG soundness trials; all 64 planted six-bit circuits exhaustively unique; recovered the planted witness in 40 capped all-mixed fixtures')
if __name__=='__main__': check()

def conflict_family(n):
    gates=[]
    def nand(a,b):
        gates.append((a,b))
        return n+len(gates)
    ys=[]
    for x in range(1,n+1):
        neg=nand(0,x)
        always=nand(x,neg)
        ys.append(nand(always,neg))
    while len(ys)>1:
        nxt=[]
        for j in range(0,len(ys),2):
            if j+1==len(ys):
                nxt.append(ys[j])
            else:
                t=nand(ys[j],ys[j+1])
                nxt.append(nand(t,t))
        ys=nxt
    final=gates.pop()
    gates.extend([(0,0)]*(4095-len(gates)))
    gates.append(final)
    return gates

if __name__=='__main__':
    g=conflict_family(128)
    trace=[]
    def take_right(*_):
        trace.append(1)
        return 1
    w=supplier(128,g,take_right)
    assert w==(1<<128)-1 and len(trace)==128 and supplier(128,g) is None
    for j in range(128):
        it=iter([int(i!=j) for i in range(128)])
        assert supplier(128,g,lambda *_:next(it)) is None
    print('4096-gate conflict family: 128 right choices succeed, switching any one of the 128 choices fails')
```

### fixtures.py

```python
from pathlib import Path
import runpy,random,sys
d=Path(__file__).parent;src=runpy.run_path(str(d/'supplier.py'))
def word(g):return b''.join(b'\x01'*(8*a+3)+b'\x00'+b'\x01'*(4*b+1)+b'\x00' for a,b in g)
def frame(v):return bytes(z for x in v for z in (1,x))+b'\x00'
p=Path('/tmp');rng=random.Random(204)
def make(k,g,tag,beta,oracle):
    assert len(g)==4096
    p.joinpath('demand204-'+tag+'.gates').write_text(','.join(str(a*8192+b) for a,b in g))
    p.joinpath('demand204-'+tag+'.bin').write_bytes(frame(frame([1]*128)*2+frame([]))+word(g)+bytes((0,1,beta,0)))
    print(tag,beta,oracle)
for tag,w in [('zeros',0),('ones',(1<<128)-1),('rand',rng.getrandbits(128)),('rand2',rng.getrandbits(128))]:
 g=src['planted'](128,w,4096);assert src['supplier'](128,g)==w
 make(128,g,tag,0 if tag=='ones' else 1,''.join(str((w>>i)&1) for i in range(128)))
for tag,g in [('conflict',src['conflict_family'](128)),('false',[(0,0)]*4096),('forward',[(4224,4224)]*4095+[(129,4224)])]:
 w=src['supplier'](128,g)
 make(128,g,tag,1,'reject' if w is None else str(w))
```

### Table.lean

```lean
import Definitions.Def_NandDemandRoles
open DemandRole SigabaNeo
def trit (n : Nat) : Option Bool := if n==0 then none else some (n==2)
def sym (b : Option Bool) : Nat := match b with | none => 0 | some false => 1 | some true => 2
def moveCode : SignType → Nat | .neg => 0 | .zero => 1 | .pos => 2
def storeCode (t : Option (Option Bool)) : Nat := match t with | none => 0 | some b => sym b+1
def main : IO Unit := do
  let mut buf:=ByteArray.empty
  for q in [:enc.states] do
    for inp in [:3] do
      for regs in [:81] do
        let ws:=fun (j:Fin 4) => trit (regs / 3^j.val %3)
        match enc.machine.tr ⟨q%enc.states,Nat.mod_lt _ (by decide)⟩ (trit inp) ws Fin.elim0 false with
        | .query x _ => nomatch x
        | .step a _ _ =>
          let n:=a.state.map Fin.val |>.getD enc.states
          let mut wr:=0
          for j in [0,1,2,3] do
            let (v,m):=a.workTapes ⟨j%4,by change j%4<4; omega⟩
            if m != (a.workTapes ⟨0,by decide⟩).2 then throw (IO.userError "unaligned")
            wr:=wr+4^j*storeCode v
          for x in [n%256,n/256,moveCode a.inputTape,moveCode (a.workTapes ⟨0,by decide⟩).2,wr,sym a.output] do
            buf:=buf.push x.toUInt8
  IO.FS.writeBinFile "/tmp/demand204.tab" buf
```

### Replay.cpp

```cpp
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <iterator>
#include <stdexcept>
#include <string>
#include <vector>
using byte=std::uint8_t;
std::vector<byte> read(const char *p){
  std::ifstream f(p,std::ios::binary); if(!f) throw std::runtime_error(p);
  return {std::istreambuf_iterator<char>(f),{}};
}
int main(int argc,char** argv){
  auto t=read(argv[1]); const unsigned states=t.size()/(3*81*6);
  if(t.size()!=states*3*81*6) throw std::runtime_error("bad table");
  for(int run=2;run<argc;++run){
    auto x=read(argv[run]);std::vector<std::array<byte,4>> w(4227);
    unsigned q=0,peak=0;int i=0,h=0;std::uint64_t steps=0;std::string out;
    while(q<states && steps<1000000000ULL){
      if(h<0 || h>4225)throw std::runtime_error("work head");
      auto &v=w[h];unsigned regs=v[0]+3*v[1]+9*v[2]+27*v[3];
      unsigned in=i<0 || static_cast<size_t>(i)>=x.size()?0:1+x[i];
      const byte *a=&t[((q*3+in)*81+regs)*6];
      q=a[0]+256*a[1];i+=a[2]-1;
      auto wr=a[4];if(wr) for(int j=0;j<4;++j){if((wr&3)!=0)v[j]=(wr&3)-1;wr>>=2;}
      h+=a[3]-1;if(h>=0 && unsigned(h)>peak)peak=h;
      if(a[5])out.push_back('0'+a[5]-1);
      ++steps;
    }
    if(q<states) throw std::runtime_error("clock exhausted");
    std::string witness;
    for(int j=1;j<=128;++j)witness.push_back(w[j][2]==2?'1':'0');
    std::cout<<argv[run]<<" "<<steps<<" "<<peak<<" "<<out<<" "<<witness<<std::endl;
  }
}
```

### CoreWord.lean

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

### Native.lean

```lean
import Definitions.Def_NandDemandRoles
open DemandRole
def main (args : List String) : IO Unit := do
  let word ← IO.FS.readBinFile args[0]!
  let mut q:=enc.machine.initial
  let mut h:=0
  let mut ip:=0
  let mut mem:Array Nat:=Array.replicate 4227 0
  let mut out:=#[]
  for i in [:enc.time] do
    let cell:=mem[h]!
    let ws:=fun (t:Fin 4) => match cell/3^t.val%3 with | 0 => none | 1 => some false | _ => some true
    match enc.machine.tr q ((word[ip]?).map (· == 1)) ws Fin.elim0 false with
    | .query e _ => nomatch e
    | .step a _ _ =>
      let mut nc:=cell
      for j in [:4] do
        let (wr,_) := a.workTapes ⟨j%4,by change j%4<4;omega⟩
        if let some b:=wr then
          let old:=nc/3^j%3
          let x:=match b with | none=>0 | some false=>1 | some true=>2
          nc:=nc-old*3^j+x*3^j
      if nc != cell then mem:=mem.set! h nc
      h:=match (a.workTapes ⟨0,by decide⟩).2 with | .pos=>h+1 | .neg=>h-1 | .zero=>h
      ip:=match a.inputTape with | .pos=>ip+1 | .neg=>ip-1 | .zero=>ip
      if let some b:=a.output then out:=out.push b
      match a.state with
      | none =>
        IO.println (out,i+1,(List.range 128).map (fun j => mem[j+1]!/9%3==2))
        return
      | some s => q:=s
  throw (IO.userError "clock")
```

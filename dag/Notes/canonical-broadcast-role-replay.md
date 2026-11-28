---
title: Reproduce the canonical tuple frames and actual registered role transitions
refs: [definition:CanonBroadcastRoles, note:canonical-broadcast-role-erratum]
tags: [witness-encryption, reproducibility]
---

Save the two listings as fixtures.py and Replay.lean. Run python3 fixtures.py. It writes two fixed-seed K91 swapped schedules to /tmp/fixture200-200 and /tmp/fixture200-201, and two K90 schedules to /tmp/fixtag200-0 and /tmp/fixtag200-1. Each tagged fixture has three free primaries; all eight assignments were enumerated to classify it before swapping. In the verified DAG Lean environment, run lake env lean --run Replay.lean emit /tmp/fixture200-200 /tmp/word.bin 0 and then lake env lean --run Replay.lean k91 /tmp/word.bin. Mode 0 encodes message one, 1 encodes zero, 2 and 3 encode decoder inputs for one and zero. Use k90 for the two tagged words and dec for a decoder tuple. The emitter calls the registered relation encStmt and encWit and the same encodeTuple as Impl.run. This test materializes the full physical word. Each physical bit is stored as one byte valued 0 or 1 in the replay file. Use the fixture helper word and frame to compare all bytes independently. An empty or truncated word and a flipped early parameter bit exercise rejection, which produces [true,false,false]. The predecessor machine can also be passed to runRoleEnc where its old DAG definition is available.

```python
from pathlib import Path
from random import Random
def templ(k,n,rs):
    gs=[]
    def emit(a,b):
        gs.append((a,b));return n+len(gs)
    for i in range(k):
        for j in range(i+2,k):rs[j]=emit(rs[i],rs[j])
    a=rs[0]
    for j in range(1,k):a=emit(a,rs[j])
    return gs,a
def tagged(ts):
    body,_=templ(90,219,list(range(130,220)))
    return [(0,0)]+[(t,t) for t in ts]+body
def accept(g,w):
    v=[1]+[w>>i&1 for i in range(128)]
    for a,b in g:v.append(1-(v[a] if a<len(v) else 1)*(v[b] if b<len(v) else 1))
    return v[-1]
def word(g):
    return b''.join(b'\x01'*(8*a+3)+b'\x00'+b'\x01'*(4*b+1)+b'\x00' for a,b in g)
def frame(v):return bytes(z for x in v for z in (1,x))+b'\x00'
def main(directory):
    for seed in (200,201):
        rng=Random(seed);g,a=templ(91,128,list(range(1,92)));g.append((a,a))
        g=[(b,a) if rng.randrange(2) else (a,b) for a,b in g]
        assert accept(g,5)
        (directory/('fixture200-'+str(seed))).write_text(','.join(str(a*8192+b) for a,b in g))
    rng=Random(2002)
    for target in (0,1):
        while True:
            inds=rng.sample(range(90),3); ts=[i+1 if i in inds else rng.choice((0,129)) for i in range(90)]
            g=tagged(ts)
            if target==any(accept(g,sum(((w>>j)&1)<<i for j,i in enumerate(inds))) for w in range(8)):break
        g=[(b,a) if rng.randrange(2) else (a,b) for a,b in g]
        (directory/('fixtag200-'+str(target))).write_text(','.join(str(a*8192+b) for a,b in g))
if __name__=='__main__':main(Path('/tmp'))
```

```lean
import Definitions.Def_CanonBroadcastRoles
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
def runRoleEnc (enc : Machine) (ht : 0<enc.tapes) (word : ByteArray) : IO (Array Bool × Nat) := do
  let mut q:=enc.machine.initial
  let mut mem : Array (Option Bool) := Array.replicate 69 none
  let mut head:=4
  let mut pos:=0
  let mut out:=#[]
  for i in [:enc.time] do
    let inp:=(word[pos]?).map (· == 1)
    match enc.machine.tr q inp (fun _ => mem[head]!) Fin.elim0 false with
    | .query e _ => nomatch e
    | .step a _ _ =>
      let (wr,mv):=a.workTapes ⟨0,ht⟩
      if let some z:=wr then mem:=mem.set! head z
      head:=match mv with | .pos => head+1 | .neg => head-1 | .zero => head
      if a.inputTape=1 then pos:=pos+1
      if let some b:=a.output then out:=out.push b
      match a.state with | none => return (out,i+1) | some z => q:=z
  throw (IO.userError "clock")
def runRoleDec (bs : ByteArray) : IO Unit := do
  let dec:=CanonicalBroadcast.dec
  let mut q:=dec.machine.initial
  let mut pos:=0
  let mut out:=#[]
  for i in [:dec.time] do
    let inp:=(bs[pos]?).map (· == 1)
    match dec.machine.tr q inp Fin.elim0 Fin.elim0 false with
    | .query e _ => nomatch e
    | .step a _ _ =>
      if let some b:=a.output then out:=out.push b
      if a.inputTape=1 then pos:=pos+1
      match a.state with
      | none => IO.println (out,i+1); break
      | some z => q:=z
def main (args : List String) : IO Unit := do
  match args with
  | ["emit",src,dst,kind] => proc200 src dst kind.toNat!
  | ["k91",src] => IO.println (← runRoleEnc CanonicalBroadcast.enc (by decide) (← IO.FS.readBinFile src))
  | ["k90",src] => IO.println (← runRoleEnc CanonicalTaggedBroadcast.enc (by decide) (← IO.FS.readBinFile src))
  | ["dec",src] => runRoleDec (← IO.FS.readBinFile src)
  | _ => throw (IO.userError "expected emit/k91/k90/dec")
```

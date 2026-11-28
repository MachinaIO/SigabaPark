---
title: Coherent nondeterministic separator certificates and private one-use grants
refs: [definition:WE_CircuitSAT_Capped, definition:RectangleGrant, theorem:AdvancedEncryption.WE.RectangleGrant.coherent, theorem:AdvancedEncryption.WE.RectangleGrant.transcript, theorem:AdvancedEncryption.WE.RectangleGrant.reconstruct]
tags: [witness-encryption, tree-decomposition, communication-complexity]
---

Let edge e have relation R_e over endpoint rows. Supply rectangles L_ec × D_ec whose union is exactly R_e. A local witness is one row per vertex satisfying its predicate P. A certificate is one c per edge and the same row at a vertex across all edge tests. The theorem coherent proves the equivalence on arbitrary incidence graphs, covering trees with any fanout. For a constructive compiler the forward search walks the public rectangle list for the first containing certificate. On groups of constraints, this applies directly if the eliminated variables are private to their factor, or a verified joint lift maps every satisfying bag/edge assignment to an original witness. Independent existentially projected equations can lose that property: the hidden bit constrained to zero on one edge and one on another has each projection true and no joint preimage. Variables shared across factors must be retained as state or included in one common realization. In an ordinary tree decomposition, agreement on the actual shared variables plus connected occurrence subtrees is sufficient for pasting the local extensions. Covering equality by bicliques needs one certificate per value: a rectangle containing distinct (a,a),(b,b) would contain the forbidden (a,b). Thus re-encoding a general shared bus by semantic covers requires a separate structural argument.

For nonempty intersection of two d-bit supports, certificates are a coordinate belonging to both. All 2^d left deterministic row types are distinct by testing singleton right supports, while d rectangles suffice and are necessary by the d singleton diagonal pairs. Even overlapping endpoint supports present no ambiguity; the witness can pick the lowest eligible coordinate. Costs of membership tests and of finding a coherent central row still matter. A coordinate certificate is evidence for compatibility, not a replacement for the row at a node.

**A finite compiler.** Split the original 128-bit witness into 32 left bits, 32 right bits, 32 central z bits and 32 central switch bits. The switch h is the parity of the fourth group. Each leaf exports the complemented input coordinates allowed by its own public mask. Mode h exports the complemented z coordinates allowed by public masks L_h and D_h. Each leaf must intersect its central support. Publicly masked coordinates are implemented by a false NAND constant, active ones by a self-NAND. The first 192 gates encode these choices independently. The remaining fixed macro syntax computes the two simultaneous intersections for each mode, selects one branch and pads to 4096 gates. The recognizer reads only these markers to infer the six masks and then validates all gates against regeneration. In particular, changing arbitrary bits of the six masks yields different members of the recognized family. The original witness computes h and selects one matching index i,j on each side of that very mode. Conversely if the abstract mask program admits a mode and an index on each side, choose all z=0, choose that parity, and choose zero leaf inputs to lift jointly. The ability to choose all z low simultaneously is an explicit part of this compiler's correctness. Independent-side reasoning without a common mode is unsound even for d=1, with mode pairs (empty,full) and (full,empty).

For each mode h sample an independent bit r_h. For each advertised side incidence (h,k,i), k=0 on the left and 1 on the right, sample one fresh pad p and always publish g=p XOR r_h XOR (k AND beta). Publish p too precisely when that leaf allows coordinate i. The layout and omitted fields are determined by public masks. One original witness reads its two grants and pads and XORs all four bits. The theorem reconstruct checks the identity. The one-use pads account for every half incidence, including unreachable uses, with no seed expansion. On a false instance choose d_h equal to the only reachable side in mode h, or arbitrary if neither side is reachable. Translate r_h by beta AND d_h and each pad by beta AND (k XOR d_h). This translates independent uniform bits bijectively. The theorem transcript shows that it fixes every published grant and every disclosed pad when translating to payload zero. Thus the *entire* NO packet has the same law, even across overlapping rectangles. No source hybrid or new cryptographic assumption is needed for the finite issuer. Generating the whole packet under one seed would require its own registered PRG hybrid and costs; a generic extension that issued inaccessible evaluators for hidden SAT predicates would be assuming the missing primitive.

Let S be the total number of incidences in all center rectangle halves and P the number whose leaf coordinate is active. Ciphertext is S+P raw bits, sampled randomness S+number of modes bits, two grants and two pads read for a valid witness. No public table indexed by all possible 32-bit supports, no online generation of a witness, no separate record per pair of coordinates. With lo the lowest 16 bits, both leaf masks high, center modes (all,lo) and (lo,all), each individual cut can pass but the two cuts have no common mode. S=96,P=32, output=128, coins=98. In the YES sibling allow bit 16 in the first mode's right half: S=97,P=33, output=130, coins=99. Both leaves still independently require the high half. A full intersection predicate over arbitrary 32-bit vectors has 2^32 row types yet 32 certificates; in these fixtures each leaf also realizes 2^16 different high supports. The phenomenon of a small join circuit alone was covered in task #253; the compiler here verifies the joint realization of overlapping nondeterministic edge certificates on one center and implements its own two-mode transcript and counts. Bit totals exclude the public circuit supplied as input and the outer single-variable frame, which adds one marker per bit plus the terminator. Native machine clocks, parsing and descriptions require separate accounting. Public mask intersections decide this restricted family directly. No uniform small-cover decomposition for arbitrary NAND statements follows.

### Finite replay

The listing below recognizes raw circuits, checks false and true instances under both payloads with actual bit grants, and exhausts 4096 small two-mode availability combinations. Gate zero is the true input and all other parents in these fixtures are available when read.

```python
from random import Random
from itertools import product

def circuit(d, leaves, halves):
    g=[]
    def nand(a,b):
        g.append((a,b))
        return 128+len(g)
    def inv(a):return nand(a,a)
    def conj(a,b):return inv(nand(a,b))
    def either(a,b):return nand(inv(a),inv(b))
    def xor(a,b):
        v=nand(a,b);return nand(nand(a,v),nand(b,v))
    def fold(f,xs):
        r=xs[0]
        for x in xs[1:]:r=f(r,x)
        return r
    def mark(mask,offset):
        return [inv(offset+i+1 if (mask>>i)&1 else 0) for i in range(d)]
    leaf=[mark(m,k*d) for k,m in enumerate(leaves)]
    part=[[mark(m,2*d) for m in row] for row in halves]
    mode=fold(xor,list(range(3*d+1,129)))
    ok=[]
    for h in range(2):
        hit=[fold(either,[conj(x,y) for x,y in zip(leaf[k],part[h][k])]) for k in range(2)]
        ok.append(conj(conj(*hit),mode if h else inv(mode)))
    w=either(*ok)
    if (4096-len(g))%2:
        inv(0)  # unused padding gate
    while len(g)<4096:w=inv(inv(w))
    assert len(g)==4096 and w==4224
    return g

def recognize(d,g):
    if len(g)!=4096:return
    m=[]
    for k,off in enumerate([0,d]+[2*d]*4):
        a=0
        for j,(x,y) in enumerate(g[k*d:(k+1)*d]):
            if x!=y or x not in (0,off+j+1):return
            a|=int(x!=0)<<j
        m.append(a)
    masks=(m[:2],[m[2:4],m[4:6]])
    return masks if g==circuit(d,*masks) else None

def evaluate(g,w):
    a=[1]+[(w>>i)&1 for i in range(128)]
    for l,r in g:a.append(1-(a[l]&a[r]))
    return a[-1]

def certificate(d,mask,w):
    leaves,halves=mask;h=(w>>(3*d)).bit_count()%2
    low=(1<<d)-1;z=~(w>>(2*d))&low
    hits=[leaves[k]&halves[h][k]&z&~(w>>(k*d)) for k in range(2)]
    if not all(hits):return
    return h,*[(x&-x).bit_length()-1 for x in hits]

def encode(d,mask,b,rng):
    leaves,halves=mask
    r=[rng.getrandbits(1) for _ in halves]
    out={};published=0
    for h,row in enumerate(halves):
        for k,m in enumerate(row):
            for i in range(d):
                if m>>i&1:
                    p=rng.getrandbits(1)
                    active=leaves[k]>>i&1
                    out[h,k,i]=(p^r[h]^(k*b),p if active else None)
                    published+=1+active
    return out,published,len(out)+len(r)

def decode(o,c):
    h,i,j=c;a,p=o[h,0,i];b,q=o[h,1,j]
    return a^p^b^q

def test():
    rng=Random(255);d=32;lo=(1<<16)-1;all=(1<<32)-1
    leaves=[all^lo]*2
    for yes in (False,True):
        mask=(leaves,[[all,lo+(int(yes)<<16)],[lo,all]])
        g=circuit(d,*mask);assert recognize(d,g)==mask
        wrong=g.copy();wrong[3]=(1,2);assert recognize(d,wrong) is None
        for b in range(2):
            o,size,coins=encode(d,mask,b,rng)
            assert (size,coins)==((130,99) if yes else (128,98))
            for w in [0]+[rng.getrandbits(128) for _ in range(128)]:
                c=certificate(d,mask,w)
                assert bool(c)==bool(evaluate(g,w))
                if c:assert yes and decode(o,c)==b
        print('YES' if yes else 'NO',size,coins)
    for l,r,u,v in product(range(4),repeat=4):
        for a,b in product(range(4),repeat=2):
            yes=bool((a&l and b&r) or (a&u and b&v))
            explicit=any((a>>i)&(m>>i)&(b>>j)&(n>>j)&1
                         for m,n in [(l,r),(u,v)] for i,j in product(range(2),repeat=2))
            assert yes==explicit

if __name__=='__main__':test()
```

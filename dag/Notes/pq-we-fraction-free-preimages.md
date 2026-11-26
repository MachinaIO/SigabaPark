---
title: Faster exact preimage sampling for the bounded WE encoder
refs: [definition:WE_CircuitSAT, note:pq-we-clocked-preimage, note:pq-we-ordered-radix-gadget]
tags: [witness-encryption, sampling, implementation]
---

Two changes speed up the bounded honest encoder without changing its coins or ciphertext. They target basis preparation and Gaussian decisions, which were excluded from the earlier matrix kernel timings. The distribution being preserved is that of the bounded reference sampler in the linked notes. Its relationship to a security-matched WE instantiation remains a separate question.

**Integer basis preparation.** Use fraction-free Gram-Schmidt (for background see [Middeke, Jeffrey and Koutschan](https://link.springer.com/article/10.1007/s11786-020-00495-9)). Let P be the Gram determinant of the completed prefix, initially one. Each remaining work vector equals P times the orthogonal residual of its original column. Write v for the next work vector; the next determinant is D=<v,v>/P. For each remaining work vector x with original column c, replace it by (Dx-<c,v>v)/P. This is D times the new orthogonal residual. The determinant and all the divisions are integral: multiplying the orthogonal projection by its prefix Gram determinant clears its denominators by the adjugate formula. In the backward sampler the exact scalar center is -<lift_current,v>/D and the squared width is sigma² P/D. This retains the earlier center and width for every possible path while doing the vector work over integers. The final two rational scalars suffice for each draw. Gram determinants and projected entries have polynomial bit length by Hadamard's inequality.

**Filtering expensive threshold evaluations.** At exponent v and precision h the earlier threshold T(v,h) differs from the real weight 2^h exp(-pi v) by at most two. Let lo=floor(32v). Monotonicity of the real exponential implies that T(v,h) lies between T((lo+1)/32,h)-4 and T(lo/32,h)+4. Compare the already sampled coin with those two certified limits. Only ambiguous coins need the full exact reference evaluation. A bounded cache of 4096 grid endpoints is reused across successive columns. This uses the same strict inequality, including at threshold ties, and consumes the same random tape on every call. Cache hits and misses affect time. These routines have data-dependent timing and are reference arithmetic for the mathematical encoder. No constant-time implementation guarantee is made.

**Measured cost.** Single-process Python on an AMD Ryzen 9 7950X3D. Three repetitions per shape; timings in milliseconds are medians. Each eight-column batch starts with an empty filter cache. Preparation is separate from drawing. The two implementations used identical public keys, lifts, widths and per-repetition random tapes. All 72 resulting columns matched exactly, had the requested syndrome and left the same final PRNG state. Each integer direction and squared Gram-Schmidt norm was checked against its rational counterpart. Another 12658 threshold comparisons exercised grid endpoints and coins at and adjacent to the exact decision boundary.

| Basis dimension | Prepare, rational | Prepare, integer | Draw eight columns, reference | Draw eight columns, optimized |
| ---: | ---: | ---: | ---: | ---: |
| 24 | 11.38 | 0.95 | 112.55 | 42.38 |
| 38 | 50.40 | 4.95 | 187.69 | 52.42 |
| 56 | 167.89 | 17.63 | 286.09 | 68.76 |

**Small complete encryption control.** We also timed a two-level, width-two encoder from fresh key generation through emission of both root blocks and both final blocks (three terminal columns retained). On the valid OR paths, the logical terminal row is (0,mu). At q=7^12 and basis dimension 112 the reference took 2825.16 ms versus 360.45 ms optimized (median of three paired runs). The measurement includes the fresh radix basis, orthogonalization, independent near-uniform terminal columns, tensor and error draws, root computation and all six preimage draws. It excludes wire serialization, decryption and certificate generation. For each run every ciphertext integer and the final PRNG state matched. These small dimensions, seeded test randomness and error parameters serve as a performance control; this is not a measured time for the previously costed large instances or a security benchmark. The acceleration has no effect on ciphertext size or on the decoder.

Run the first listing with the sample_squared and threshold routines from the revised clocked preimage listing. The optional predicate in sample_squared substitutes an exactly equivalent threshold comparison.

~~~python
from fractions import Fraction

def inner(a,b):
    return sum(x*y for x,y in zip(a,b,strict=True))

def exact_div(n,d):
    q,r=divmod(n,d)
    if r:
        raise ArithmeticError("nonintegral projection")
    return q

def gram_prepare(cols):
    work=[list(col) for col in cols]
    prefix=1
    directions=[]
    for i,v in enumerate(work):
        det=exact_div(inner(v,v),prefix)
        if not det:
            raise ValueError("dependent basis")
        directions.append((v,prefix,det))
        for j in range(i+1,len(work)):
            u=work[j]
            cross=inner(cols[j],v)
            work[j]=[exact_div(det*x-cross*y,prefix) for x,y in zip(u,v,strict=True)]
        prefix=det
    return directions

def gram_draw(cols,dirs,lift,sigma2,b,bits,sample_squared):
    x=list(lift)
    for j in reversed(range(len(cols))):
        v,prev,det=dirs[j]
        center=Fraction(-inner(x,v),det)
        width2=Fraction(sigma2)*prev/det
        z=sample_squared(center,width2,b,bits)
        if z:
            x=[a+z*t for a,t in zip(x,cols[j],strict=True)]
    return x

from functools import lru_cache

def filtered_sampler(sample_squared,threshold):
    @lru_cache(maxsize=4096)
    def edge(i,h):
        return threshold(Fraction(i,32),h)

    def accept(v,h,coin):
        lo=(32*v).__floor__()
        if coin>=edge(lo,h)+4:
            return False
        if coin<edge(lo+1,h)-4:
            return True
        return coin<threshold(v,h)

    def draw(center,width2,b,bits):
        return sample_squared(center,width2,b,bits,accept=accept)
    return draw
~~~

To reproduce the measurements, save the first listing as ff_gpv.py and run the following two scripts separately from the DAG repository root.

~~~~python
from fractions import Fraction as F
from random import Random
from statistics import median
from time import perf_counter
import runpy
base={}
from pathlib import Path
p=Path('dag/Notes/pq-we-clocked-preimage.md')
exec(p.read_text().split('~~~python\n')[1].split('~~~')[0],base)
radix={}
exec(Path('dag/Notes/pq-we-ordered-radix-gadget.md').read_text().split('~~~python\n')[1].split('~~~')[0],radix)
radix['radix_setup'].__globals__['dot']=base['dot']
ff=runpy.run_path('ff_gpv.py')
for n,q,a in ((1,17,2),(2,127,3),(3,257,3)):
    A,B,lift=radix['radix_setup'](n,q,6,a,Random(300+n).getrandbits)
    ref=base['orthogonalize'](B)
    fast=ff['gram_prepare'](B)
    for (u,norm),(v,prev,det) in zip(ref,fast):
        assert [F(x,prev) for x in v]==u and F(det,prev)==norm
    m=len(B);sigma2=16*max(norm for _,norm in ref)
    times=[[] for _ in range(4)]
    for repeat in range(3):
        targets=[[Random(400+j+i*17+repeat*91).randrange(q) for i in range(n)] for j in range(8)]
        for idx in range(2):
            t0=perf_counter()
            dirs=ff['gram_prepare'](B) if idx else base['orthogonalize'](B)
            times[idx].append(perf_counter()-t0)
            coins=Random(700+repeat)
            out=[]
            sampler=ff['filtered_sampler'](base['sample_squared'],base['threshold'])
            t0=perf_counter()
            for y in targets:
                args=(B,dirs,lift(y),sigma2,8,coins.getrandbits)
                out.append(ff['gram_draw'](*args,sampler) if idx else base['preimage'](*args))
            times[idx+2].append(perf_counter()-t0)
            if idx:
                assert out==expected and coins.getstate()==expected_state
                assert all([base['dot'](r,x)%q for r in A]==y for x,y in zip(out,targets))
            else:
                expected=out;expected_state=coins.getstate()
    print(m,*[round(1000*median(t),2) for t in times],flush=True)
~~~~

~~~~python
from fractions import Fraction as F
from itertools import product
from random import Random
from statistics import median
from time import perf_counter
import runpy
from pathlib import Path
g={}
for name in ('pq-we-clocked-preimage','pq-we-ordered-radix-gadget'):
    s=Path('dag/Notes/'+name+'.md').read_text()
    exec(s.split('~~~python\n')[1].split('~~~')[0],g)
ff=runpy.run_path('ff_gpv.py')
def encrypt(mu,seed,fast):
    rng=Random(seed)
    bits=rng.getrandbits
    q=7**12
    a=3
    A,cols,lift=g['radix_setup'](2,q,5,a,bits)
    m=len(cols);ell=2*((((q-1).bit_length())+a-1)//a)
    T=8+(m-1).bit_length()+4
    sigma2=g['radix_quality'](m-ell,a)*T
    dirs=ff['gram_prepare'](cols) if fast else g['orthogonalize'](cols)
    # Retain three terminal columns of an independent near-uniform matrix.
    terminal=[[bits((q-1).bit_length()+16)%q for _ in range(3)] for _ in range(2)]
    draw=ff['filtered_sampler'](g['sample_squared'],g['threshold']) if fast else g['sample_squared']
    def entry(width):
        return draw(F(0),width**2,8,bits)
    root=[];end=[]
    for b in (0,1):
        s=entry(8)
        root.append([(s*((1-b)*x+mu*y)+entry(2))%q for x,y in zip(*A)])
    for b in (0,1):
        s=entry(8)
        block=[]
        for f,u in zip(*terminal):
            target=[(s*(1-b)*f+entry(2))%q,(s*u+entry(2))%q]
            args=(cols,dirs,lift(target),sigma2,T-3,bits)
            block.append(ff['gram_draw'](*args,draw) if fast else g['preimage'](*args))
        end.append(block)
    return (root,end),rng.getstate(),m
times=[[],[]]
for mu,seed in [(0,714),(1,815),(1,918)]:
    for i in (0,1):
        start=perf_counter()
        out,coins,m=encrypt(mu,seed,i)
        times[i].append(perf_counter()-start)
        if i: assert (out,coins)==reference
        else: reference=(out,coins)
print('complete encoding',m,*[round(1000*median(t),2) for t in times])
~~~~

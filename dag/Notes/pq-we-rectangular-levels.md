---
title: Rectangular tensor levels from simultaneous witness-state widths
refs: [definition:WE_CircuitSAT, note:pq-we-unit-output-clause-groups, note:pq-we-quantum-preimage-hop, note:pq-we-root-loss-budget]
tags: [witness-encryption, compilation, complexity, correctness]
---

A width maximum at a single level sets the cost of *every* square transition in the preceding tensor estimate. Allow a separate logical width at each cut. This changes the shapes of the public lattice keys and ciphertexts. The fixed-width published hiding theorem cannot be invoked just by dropping entries of its ciphertext.

**Public compiler.** For each cut, propagate a basis of all attainable rows, spanning both possible initial message rows. Basis propagation under the two branches is exact by linearity. A coordinate that vanishes on every basis row always vanishes. Two columns equal on the basis give identical coordinate functions on all original paths and both messages. Drop the zero columns and keep one representative per equal class. For each destination representative keep its original incoming edges, reindexing the sources by their equivalence classes. In the unit-output group compiler every reachable entry is zero or one. Two live equal source functions cannot both contribute to one destination on the same branch: some attainable prefix has both equal to one, giving an impossible destination value of at least two. Thus the reindexed transitions are binary; the listing explicitly checks this property. The initial row and every next row are the original row restricted to representatives. Restoring zero and duplicate columns at the end recovers every original terminal coefficient. In particular a unit survives on each false path. All maps, dimensions and edge sets are derived jointly for both messages. In the test corpus the peak width stayed unchanged, so padding back to one fixed width gave no payload improvement.

**Rectangular encoder.** Write w_i for width after choice i, r_i=n w_i, and A_i for the r_i by m_i public matrix. At level one the encoded factor is (u M_1,b) tensor S_1,b of shape n by r_1. For later levels F_i,b=M_i,b tensor S_i,b has shape r_(i-1) by r_i. Draw the same type of fresh tensor factors and errors at the specified dimensions. Send the root residue blocks F_1,b A_1+E_1,b, and use the preceding key to sample each column of D_i,b with A_(i-1) D_i,b = F_i,b A_i+E_i,b mod q. Each block now has m_(i-1) rows and m_i columns. Along a selected path the exact residual update remains e_i=e_(i-1)D_i+P_(i-1)E_i, where P_(i-1) is the ideal prefix factor. Stage-specific column norm bounds from A_(i-1) enter this recurrence. Tensor survival is governed by the dimension n of the S factors. For terminal shortness or modulus selection use the actual logical prefix norms or a conservative common bound; dimensions alone do not prove an error-bit claim.

**Accounting.** The full-root raw payload per message bit is 2k(n m_1+sum_(i>=2) m_(i-1)m_i) bits, with k=ceil(log2 q). Enc samples 2 sum_(i>=2) m_i preimage columns in addition to setup, target formation and noise. Dec uses n sum_(i>=2) m_(i-1)m_i modular multiply-adds plus scanning and projecting the witness. Setup and drawing are at different dimensions across levels. Fixed-budget packing can separately price the m_(i-1)-entry columns at each level. Polynomial w_i, n, k and clocked samplers give polynomial honest costs. These comparisons exclude public metadata and preprocessing.

**Conditional security interfaces.** At prefix i the isolated table takes an r_i by m_i uniform public matrix. Its projected rows use w_i logical coefficients and the same n by n factor product as before. In the hop linking it to level i+1, the stacked prefix secret has 2^i n rows and r_i columns; the two concatenated targets have r_i rows and 2m_(i+1) columns. The fresh hidden key is r_i by m_i. The flooding shift consequently has 2m_(i+1) columns, while the isolated table's moment has m_i. The quantum preimage-purge reduction at this hop must generate its split hidden key at total width m_i, with 2m_(i+1) ordinary LWE samples per secret and r_i secret rows, under that reduction's smoothing and trapdoor bounds. The root PRE-to-POST assumption has to cover these unequal dimensions and the joint suffix. In particular checking only a square challenge or identical LWE parameters for every cut does not establish hiding for this variant. A floor imposed by a security proof on any m_i or r_i must be reflected in the accounting before claiming a security-matched gain.

**Controls.** On the same 60 four-input five-NAND circuits, using the grouped unit-output compiler with cap four, H=9, n=4, k=32 and m_i=2r_i k, the total arithmetic accounts are:

| Representation | Full-root payload bits | Preimage columns | Dense Dec multiply-adds |
| --- | ---: | ---: | ---: |
| Previous peak-width padding | 106764500992 | 1740800 | 6671040512 |
| Rectangular, keep each group's active states | 68161110016 | 1368576 | 4259053568 |
| Rectangular, also identify equal live coordinates | 66312667136 | 1358848 | 4143710208 |

Most of the reduction comes from dimensioning keys per level. These small circuits were publicly solvable by an earlier compiler; this experiment prices the general matrix encoding and is not a benchmark at secure dimensions. All 61440 circuit/witness/message combinations reconstructed the previous terminal row exactly. A separate three-level encoding checked real bounded Gaussian preimages using the prior fraction-free sampler, with transmitted shapes 2 by 48, 48 by 30 and 30 by 3 (three terminal columns retained). Across three seeds every target congruence and each of the eight path residual identities matched. The toy q=17 test checks algebra, not a failure or hiding probability.

The first listing uses independent from the contextual interval note. Run the second listing from the DAG root after saving the first listing as layer_width.py. The third listing uses existing sampler listings directly.

~~~python
def reduce_layers(row,layers,independent):
    w=len(row)
    # Coordinate zero carries the message; span both public initializations.
    basis=independent([tuple([mu]+row[1:]) for mu in (0,1)])
    def classes(rows):
        reps=[];ids={};mapping=[]
        for i,signature in enumerate(zip(*rows)):
            if not any(signature):
                mapping.append(None)
            else:
                if signature not in ids:
                    ids[signature]=len(reps);reps.append(i)
                mapping.append(ids[signature])
        return reps,mapping
    reps,mapping=classes(basis)
    init=[[([mu]+row[1:])[i] for i in reps] for mu in (0,1)]
    widths=[len(reps)];compact=[]
    for pair in layers:
        candidates=[]
        for edges in pair:
            for u in basis:
                v=[0]*w
                for i,j in edges:v[j]+=u[i]
                candidates.append(tuple(v))
        basis=independent(candidates)
        new_reps,new_mapping=classes(basis)
        keep={j:k for k,j in enumerate(new_reps)}
        out=[]
        for edges in pair:
            dest=set()
            for i,j in edges:
                if j in keep and mapping[i] is not None:
                    edge=(mapping[i],keep[j])
                    if edge in dest:
                        raise ValueError("binary representative would have multiplicity")
                    dest.add(edge)
            out.append(dest)
        compact.append(out)
        mapping=new_mapping
        widths.append(len(new_reps))
    return init,compact,widths,mapping

def resources(widths,n,k):
    # VWW-style full roots and final blocks; key rank after level i is n*w_i.
    m=[2*n*w*k for w in widths[1:]]
    pairs=sum(a*b for a,b in zip(m,m[1:]))
    return (2*k*(n*m[0]+pairs),2*sum(m[1:]),n*pairs)
~~~

~~~~python
from pathlib import Path
from random import Random
import runpy
g={}
exec(Path('dag/Notes/pq-we-unit-output-clause-groups.md').read_text().split('~~~python\n',1)[1].split('\n~~~',1)[0],g)
front={}
s=Path('dag/Notes/pq-we-live-clause-matrix-product.md').read_text()
exec(s.split('~~~python\n')[1].split('def run_tests')[0],front)
from itertools import product
from fractions import Fraction
sf={}
exec(Path('dag/Notes/pq-we-contextual-interval-products.md').read_text().split('~~~python\n',1)[1].split('\n~~~',1)[0],sf)
red=runpy.run_path('layer_width.py')
def eval_row(r,layers,bits,widths):
    for pair,bit,w in zip(layers,bits,widths):
        nxt=[0]*w
        for i,j in pair[bit]:nxt[j]+=r[i]
        r=nxt
    return r
rng=Random(712)
totals=[[0,0,0] for _ in range(4)]
num=0;examples=[]
for _ in range(60):
    C=front['nand_cnf'](4,[(rng.randrange(5+j),rng.randrange(5+j)) for j in range(5)])
    gs,row,old=g['pack_groups'](C,9,4);w=len(row)
    init,new,widths,restore=red['reduce_layers'](row,old,sf['independent'])
    for bits in product((0,1),repeat=9):
        for mu in (0,1):
            answer=eval_row(init[mu],new,bits,widths[1:])
            actual=eval_row([mu]+row[1:],old,bits,[w]*9)
            assert [0 if j is None else answer[j] for j in restore]==actual
            num+=1
    examples.append((w,widths))
    live=[len(gs)+1]+[1+sum(len(g["dfa"](c,9,4)[i]) for c in gs) for i in range(1,9)]+[len(gs)+1]
    for t,ws in zip(totals,[[w]*10,[max(widths)]*10,live,widths]):
        for j,v in enumerate(red['resources'](ws,4,32)):t[j]+=v
print(num,totals,examples[0])
~~~~

~~~~python
from itertools import product
from pathlib import Path
from random import Random
import numpy as np
ns={}
for s in ('clocked-preimage','ordered-radix-gadget','fraction-free-preimages'):
    p=Path('dag/Notes/pq-we-'+s+'.md')
    exec(p.read_text().split('~~~python\n',1)[1].split('\n~~~',1)[0],ns)
def check(seed):
    q=17;n=2;a=2
    bits=Random(seed).getrandbits
    draw=ns['filtered_sampler'](ns['sample_squared'],ns['threshold'])
    def small():return draw(0,4,5,bits)
    def mat(rows,cols,fn):return np.array([[fn() for j in range(cols)] for i in range(rows)],dtype=object)
    def key(w):
        A,cols,lift=ns['radix_setup'](n*w,q,4,a,bits)
        m=len(cols);ell=n*w*(((q-1).bit_length()+a-1)//a)
        T=8+(m-1).bit_length()+4
        sig2=ns['radix_quality'](m-ell,a)*T
        dirs=ns['gram_prepare'](cols)
        def pre(y):return ns['gram_draw'](cols,dirs,lift(y),sig2,T-3,bits,draw)
        return np.asarray(A,dtype=object),pre
    widths=(2,1,2)
    prev=None;public=[];ct=[];factor=[];noise=[]
    for j,w in enumerate(widths):
        if j+1<len(widths):A,next_pre=key(w)
        else:A,next_pre=mat(n*w,3,lambda:bits(20)%q),None
        public.append(A);C=[];F=[];E=[]
        for b in (0,1):
            M=mat(widths[j-1] if j else 1,w,lambda:bits(1))
            S=mat(n,n,small)
            Z=np.kron(M,S)
            err=mat(len(Z),A.shape[1],small)
            y=(Z@A+err)%q
            D=np.array([prev(list(col)) for col in y.T],dtype=object).T if j else y
            if j:assert np.array_equal(public[j-1]@D%q,y)
            F.append(Z);C.append(D);E.append(err)
        factor.append(F);ct.append(C);noise.append(E);prev=next_pre
    for path in product((0,1),repeat=3):
        val=ct[0][path[0]];P=factor[0][path[0]];e=noise[0][path[0]]
        for j,b in enumerate(path[1:],1):
            val=val@ct[j][b]%q
            e=e@ct[j][b]+P@noise[j][b]
            P=P@factor[j][b]
        assert np.array_equal(val,(P@public[-1]+e)%q)
    return [c[0].shape for c in ct]
print([check(i) for i in range(3)])
~~~~

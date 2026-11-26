---
title: Classical-sample quantum hybrids and an exact flooding moment for prefix products
refs: [definition:WE_CircuitSAT, note:pq-we-quantum-preimage-hop, note:pq-we-tensor-rank-survival]
tags: [witness-encryption, reduction, complexity, correctness]
---

**Target.** In the root argument of [VWW, Lemmas 5.2 and 5.3](https://ntt-research.com/wp-content/uploads/2023/01/Witness-encryption-and-null-iO-from-evasive-LWE.pdf) the precondition involves noisy tables at multiple prefix depths. Here is an explicit classical-sample proof for the prefix-product distribution at any fixed depth j. It applies to a bit transition pair M_i,b of width w, binary initial row u, independent n-by-n factor entries of mean zero and variance v, and r=wn rows in the initially uniform matrix A with m columns. Write alpha_x=u M_1,x1 ... M_j,xj, using integer arithmetic. Assume each terminal row at full depth generates the unit ideal modulo q on the false statement. Every prefix also generates it: later right-multiplication cannot enlarge the ideal of row entries. This formulation handles composite q without treating every nonzero scalar as a unit.

**Noisy tree.** To build the table for depth j, split A into w uniform n-by-m blocks. Start with this single parent and prepend factors in the order j,j-1,...,1. For each parent block V and branch b emit S_i,b V+E_child modulo q with a fresh independent entrywise error matrix. Share S_i,b across all parents and all w blocks at this level. The two branch outputs use the same parent. Project the w leaf blocks along alpha_x, and add a fresh independent entrywise Gaussian of width f to each leaf's projected matrix. All factor matrices may be given to the distinguisher. Unused factor levels are sampled independently.

**Statistical switch with shared randomness.** The desired table contains the noiseless factor products followed by that same final Gaussian. For fresh integer errors of mean zero and variance e, the expected squared Euclidean norm of the entire shift introduced by the noisy tree is exactly

    L_j = n m (sum_x ||alpha_x||²) e sum_{k=0}^{j-1}(n v)^k.

Use the natural integer error expansion even though actual matrices are reduced modulo q. Along one path, fresh errors add variance e per coordinate. Multiplication by the next independent factor multiplies the mean squared entry by nv, since different factor entries have zero cross moments. Conditional on all factors, errors from different logical blocks are centered and independent; summing along alpha_x contributes its squared norm. Summing expected squared entries across the table does not require independence of different paths. For a fixed integer shift z the relative entropy between the product discrete Gaussian and its translate is pi ||z||²/f² in the exp(-pi ||x||²/f²) convention, by symmetry and cancellation of the normalizer. Pinsker, averaging and Jensen bound total variation by sqrt(pi L_j/2)/f. This also bounds the joint view with the public factors, and remains valid modulo q. Any bounded-sampler approximation must be added if these ideal laws are replaced. The logical energy can be computed without enumerating the table: start with Q=u-transpose times u and update Q by summing M_b-transpose Q M_b over both branches. Its trace is the required sum. This costs O(j w³) integer operations. It improves parameter accounting; the computational reduction itself still materializes exponentially many rows.

**Quantum distinguisher for a classical table.** Replace the generated frontier with independent uniform blocks one level at a time, starting from the uniform root. At level i the short public LWE design is the n-by-2n transpose of the stacked pair (S_i,0; S_i,1). Each parent column is an independent uniform secret. The two children of that column form one classical LWE response with independent errors. For a frontier of t parents there are t w m independent secrets using that *same* design. A row hybrid embeds one challenge secret, while all remaining responses are either drawn directly as uniform or calculated using known secrets. The wrapper generates the rest of the tree and invokes the quantum distinguisher on its classical input once. The total one-secret advantage loss is bounded by (2^j-1)wm times the maximal short-design LWE advantage at the wrapper's actual time and sample count. In the final hybrid all leaf blocks are independent uniform conditional on all public factors. Since each alpha_x generates the unit ideal, the projected outputs are independent uniform, even with the final additive noise. This proves the target comparison up to the computational and statistical terms above. It makes no claim of a PRF secure against coherent oracle queries; this proof concerns explicit classical tables in the WE reduction.

**When ordinary quantum LWE suffices for this tree.** There is also a parameter-dependent way to implement the design switch with ordinary uniform-public-matrix LWE. At one level take U uniform of shape d by 2n and a multi-secret response Y=T U+E or uniform. Draw a hidden d-by-n trapdoor matrix H and sample each of 2n columns of P from the desired factor Gaussian conditioned on HP=U. The two n-by-n halves of P encode the transposed branch matrices. Draw an independent uniform mask W of shape (twm)-by-n, and deliver P and Y+WP. In the real experiment TH+W is uniform independent of P,H,T,E; this gives precisely short-design responses with uniform secrets up to the marginal error of P. In the uniform experiment the response stays uniform independent of P. With syndrome probability ratio R on a good H, the difference from the required independent factor-entry law costs at most 2n(R-1) per endpoint, plus bad-key and sampler errors. Lift once per level for the multi-secret experiment, then reduce that ordinary multi-secret challenge to twm ordinary one-secret challenges sharing U. No factor-law error need be multiplied by the number of parent columns. This requires a working trapdoor sampler for H at the *factor* Gaussian width and dimensions, e.g. sufficiently many columns n compared with d log q and a sufficiently wide Gaussian. The bounded sampler and smoothing bounds from the preceding notes provide sufficient conditions in their respective regimes. This route does not justify the constant-width original tensor factors or the dimension-one correctness control. For narrow factors one still needs the appropriate short-design result at quantum hardness parameters. Enlarging factors must also be charged to the honest errors and other proof steps.

**What remains.** For the sampler family actually used at each VWW induction level, a quantitative quantum evasive-LWE PRE-to-POST implication is still required. This prefix result supplies one computational input to that implication. The induction must absorb the flooding and dimension losses at every invocation; no global PQ security theorem or concrete security-bit claim is made. The ordinary LWE assumption in the widened route must hold at the base dimension d, with 2n samples per secret, the chosen error law, and the potentially exponential wrapper runtime. Selecting d from a correctness target alone would not supply such hardness.

**Checks and example.** Direct expansion verified 60 logical energy values on finite programs. Exact enumeration verified the complete joint squared-shift mean on a shared-sign two-level binary tree (16384 outcomes), and on a two-dimensional single path with two blocks (4096 outcomes). In the eight-level example in the listing below the logical energy is 4864; n=4,m=16,v=e=1 give mean square 6800261120 and 8160 one-secret replacements. The conservative integer Gaussian width 500884570564991 makes this particular flooding term at most 2^-32. These are proof parameters for the example, not an encryption benchmark.

~~~python
from fractions import Fraction
from math import isqrt

def program_energy(initial,levels):
    # Q is the sum of outer products of all logical rows at the current level.
    w=len(initial)
    Q=[[a*b for b in initial] for a in initial]
    totals=[]
    for pair in levels:
        nxt=[[0]*w for _ in range(w)]
        for M in pair:
            QM=[[sum(Q[i][k]*M[k][j] for k in range(w)) for j in range(w)] for i in range(w)]
            for i in range(w):
                for j in range(w):
                    nxt[i][j]+=sum(M[k][i]*QM[k][j] for k in range(w))
        Q=nxt
        totals.append(sum(Q[i][i] for i in range(w)))
    return totals

def prefix_budget(initial,levels,n,m,var_factor,var_fresh,bits):
    energy=program_energy(initial,levels)
    variance=Fraction(0)
    result=[]
    for j,U in enumerate(energy,1):
        variance=var_fresh+n*Fraction(var_factor)*variance
        mean_square=n*m*U*variance
        # pi/2 < 2. With this integer width the shift error is <= 2^-bits.
        z=2*mean_square*(1<<(2*bits))
        width=isqrt((z.numerator+z.denominator-1)//z.denominator)
        if width*width<z:
            width+=1
        result.append((U,mean_square,max(1,width),len(initial)*m*((1<<j)-1)))
    return result
~~~
~~~python
from itertools import product
from random import Random
from math import gcd
from fractions import Fraction as F
import runpy
g=globals()  # execute after the first listing
rng=Random(12);checks=0
for w,H in product([1,2,3,4],[1,2,3,4,5]):
    u=[rng.randrange(2) for _ in range(w)]
    levels=[[[[rng.randrange(2) for _ in range(w)] for i in range(w)] for b in range(2)] for j in range(H)]
    E=g['program_energy'](u,levels)
    rows=[u]
    for (left,right),e in zip(levels,E):
        rows=[[sum(a*b for a,b in zip(row,col)) for col in zip(*M)] for row in rows for M in (left,right)]
        assert sum(sum(x*x for x in row) for row in rows)==e
        checks+=1
print('energy prefixes',checks)
# Two levels, two logical coordinates, scalar factors. Use all shared random signs.
alpha=[[1,2],[2,0],[0,1],[2,1]]  # listed by first bit then second bit
total=0
for coins in product((-1,1),repeat=14):
    S=coins[:2];inner=coins[2:6];outer=coins[6:]
    for i,j in product(range(2),repeat=2):
        path=2*i+j
        d=[S[i]*inner[2*j+t]+outer[2*path+t] for t in range(2)]
        total+=sum(x*y for x,y in zip(d,alpha[path]))**2
assert F(total,1<<14)==2*sum(sum(x*x for x in row) for row in alpha)
# Dimension two, two levels, a single path and two independent blocks.
total=0
for coins in product((-1,1),repeat=12):
    S=coins[:4];e=coins[4:8];f=coins[8:]
    for i in range(2):
        total+=sum(a*(sum(S[2*i+t]*e[2*k+t] for t in range(2))+f[2*k+i]) for k,a in enumerate([1,2]))**2
assert F(total,1<<12)==2*5*(1+2)
print('two exhaustive moment identities')
print('sample',g['prefix_budget']([1,0],[[[[1,0],[0,1]],[[1,1],[0,1]]]]*8,4,16,1,1,32)[-1])
~~~

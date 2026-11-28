---
title: Exact affine-slice gain and a nearly tight signed lower bound on the registered NAND alphabet
refs: [definition:WE_CircuitSAT_Capped, note:optimal-anchored-quadratic-fiber-filter]
tags: [witness-encryption, additive-combinatorics, fourier-analysis]
---

Let S=x0+V be a nonempty affine syndrome slice; if it is empty then linear elimination already certifies NO. Let A be its nonempty subset of accepting feature words. Allow all off-slice signed Fourier coefficients to vary. On S prescribe signed response c s(a) at each a in A, with any fixed s(a) in {-1,1}, and zero on S outside A. The exact optimum over error laws is the reciprocal spectral norm

    N(A,s) = E_{y in V*} | sum_{a in A} s(a) (-1)^{y·(a-x0)} |.

Indeed twist the error signed measure by the character x0 and push it to the dual quotient by V-perp. This contraction in total variation has precisely the above Walsh coefficients scaled by c. Fourier inversion forces its norm to equal c N(A,s), hence at most one. Conversely at equality lift the quotient measure by one arbitrary representative per coset, untwist, and sample mass with the prescribed sign. The remaining independent linear constraint masks and scalar correction then give exactly equal full public laws on NO. Existence here allows instance-dependent sampling of the accepting set's Fourier data. The magnitude at saturation gives disjoint bit-conditioned packet supports on YES; it is the sign of the full character sum that reads the complete view. Constructing these distributions or evaluating that sign efficiently on all circuits remains open. A single known witness reads its own signed parity with bias c. No full-view impossibility follows from a small c. By Parseval and Cauchy--Schwarz, N<=sqrt(|A|), so unconstrained sampling can always achieve at least 2^-64 for the 128-input problem. Each bitstring gives at most one accepting trace.

For positive witness signs, gain 1 is possible exactly when A is affine. In the affine case all characters add coherently on its annihilator and vanish off it, giving norm one. Otherwise there are three words a,b,c in A with d=a+b+c outside A but inside S. A sample parity at d is the product of the three signed sample parities since the common sign bit occurs three times. Its correlation with any fixed target sign is zero, hence half its values disagree with the product of the three desired signs. The union bound forces c<=2/3 even for variable witness signs. Three points of an affine plane attain 2/3 with positive signs. With unit gain and an efficient issuer, collect dim(V)+k independent known-bit samples and enforce the known-bit linear parity equations jointly with HX=d. Every valid word remains, every invalid word survives with probability 2^(-dim(V)-k), so with probability at least 1-2^-k solving the system recovers a valid word. For arbitrary signs this recovery statement requires that the signing linear functional be known (positive signs in particular).

A worst-case circuit nearly attains the general square-root bound even allowing both arbitrary signs on witnesses and circuit-dependent off-slice relaxation. On each of two separate groups of 64 inputs put all 2016 unordered pairs through NAND; fill the remaining 64 gates with constants giving true output. Each group exposes the linear and all pair-product coordinates of u up to affine translations. The map F(u)=(u,(u_i u_j)_{i<j}) has Sidon image: if four distinct image points sum to zero the linear part is an affine square of independent directions h,k, and its quadratic part gives h_i k_j+h_j k_i=0 for every pair. All minors vanish, contradicting independence. Hence a group of size N=2^64 has 3N²-2N ordered zero-sum quadruples (equal-pair patterns). Additional feature coordinates can only remove quadruples. The joint image has second moment of its signed character sum Z equal to N², and fourth moment at most (3N²-2N)² for ALL choices of signs even when the signs correlate between the groups. These moments may be computed in the ambient dual: an anchored affine translation changes only an overall sign, and quotient-uniform characters after twisting give the same absolute values. Holder now gives

    E|Z| >= (E Z²)^(3/2)/sqrt(E Z^4) >= N²/(3N-2).

Thus c <= (3N-2)/N² < 3·2^-64. With four groups of 32 inputs the factor is less than 9 instead of 3, even if every one of the registered gates must syntactically reach the output: 1984 pair NANDs, 1983 gates reducing them by a NAND chain, 127 repeated-input NOTs, one NOT on that result U, and NAND(U,NOT(U)). The final output is tautological, so public YES simplification is an immediate alternative. The bound concerns a single prescribed parity response on all trace words, and does not price nonlinear decoding or imply hardness of the example. No fixed computational assumption is introduced.

There is a separate density test on the underlying random-code proposal. A uniform affine subspace of codimension k<=8322 in the 4225-square binary matrix space has expected rank-one intersection size mu=(2^4225-1)^2/2^k, about 2^128 even at maximum k. For two distinct points, conditional membership of the second given the first has probability (2^(4225^2-k)-1)/(2^(4225^2)-1)<=2^-k. Thus Var<=mu and the probability of an empty intersection is at most 1/mu. Every unsatisfiable circuit lies in this rare class, invariant under ordinary rank-preserving affine-space coordinate changes that preserve matrix rank. This is a statistical gap, not a polynomial-time distinguisher. Appending a fixed identity block of size l raises the dimension and allowed rank together and preserves both the affine dimension and the determinantal codimension (n-r)^2. Simply adding 128 fresh independent hash rows (at maximum original k) can reduce random expected rank-one count below one. A fixed true witness survives a fresh random bucket with probability 2^-128. Explicitly issuing every such bucket crosses the 2^100 cap before assigning any nontrivial work per bucket. Neither argument excludes an efficient correlated succinct embedding into the primary paper's planted problem.

Executable check of the pair-sum property and spectral lower bound for a signed two-clique fixture:

```python
from collections import Counter
from itertools import combinations
def words(n):
    return [x + sum((((x>>i)&(x>>j)&1)<<(n+k))
                    for k,(i,j) in enumerate(combinations(range(n),2)))
            for x in range(1<<n)]
for n in (1,2,3,4):
    ws=words(n)
    ps=Counter(x^y for x in ws for y in ws)
    N=len(ws)
    assert sum(v*v for v in ps.values())==3*N*N-2*N
w=words(2)
xy=[a+8*b for a in w for b in w]
for seed in range(16):
    signs=[(-1)**(((a+1)*(seed+7)).bit_count()%2) for a in xy]
    z=[sum(s*(-1)**((a&y).bit_count()%2) for a,s in zip(xy,signs)) for y in range(64)]
    assert sum(t*t for t in z)==64*16 and sum(t**4 for t in z)<=64*40**2
    assert sum(abs(t) for t in z)*10>=64*16
```


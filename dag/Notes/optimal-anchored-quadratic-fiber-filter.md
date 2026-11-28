---
title: Optimal flat signed filters for sparse anchored equal-factor fibers and their rectangular interpolation
refs: [definition:WE_CircuitSAT_Capped, note:rank-one-nand-fibers-and-random-minrank]
tags: [witness-encryption, quadratic-forms, fourier-analysis]
---

Use the distinct feature vector v(x)=(1, x_i, x_i x_j for {i,j} in G) where G is the graph of genuine distinct nonconstant parent pairs. The NAND constraints are still affine in these features; squares and constant products are linear. The public mask now uses at most 1+4224+4096=8321 coefficients plus one signed body, instead of a 4225-square matrix. Repeated parent pairs use one coefficient; compute the witness feature vector on demand. Up to 4096 native NANDs and 4096 two-bit products plus one scalar product suffice after parsing. No 8321-bit claim includes distributing repeated copies or the clock to sample errors.

Consider any signed probability error on the feature space with Fourier response c at every v(x) and zero at all other frequencies except optionally zero. This is a constraint on a universal prebaked filter, stronger than privacy on just the circuit's syndrome slice. The inverse kernel is K=(-1)^a W_B(l), W_B(l)=sum_x (-1)^(q_B(x)+l·x), where (a,l,B) are uniform affine constant, linear mask and independent coefficients on the edges of G. A free response at zero cannot improve the minimal expected absolute value because a fair a makes K symmetric and zero a median. For alternating polar matrix B of rank r, W_B(l)^2 equals 2^n times the sum over radical vectors h of (-1)^(q_B(h)+l·h), by writing a pair x,x+h. Thus it has magnitude 2^(n-r/2) on exactly 2^r compatible linear forms, zero elsewhere. Fourier inversion and total variation give the exact optimum
          
    c_max = 1/M(G),    M(G)=E_B[2^(rank(B)/2)].

Equality as an unrestricted signed sampler follows by using mass proportional to |K| and its sign. A concrete approximately tilted implementation was explored in the earlier frontier rank-weight work. Here a bounded-fair fallback chooses B uniformly, picks l uniformly among forms satisfying the radical equations, and gives the sign of K with conditional expected multiplier 2^(r/2-h), using fair coins and a random sign outside the retained event, where h bounds r/2. Choose the affine constant uniformly. Its signed density equals K/2^h with respect to uniform (verify on its support by the density factor 2^(n-r)). The value and sign of a quadratic Gauss sum are available by symplectic elimination. Straight dense elimination requires O(n^3) bit operations and O(n^2) temporary bits per packet without a native tape certification. Independent repetition for a witnessed bias c takes order c^-2 copies. For the complete pair graph the dyadic guarantee with n=4224 is 2^-2112. Rectangular full-rank noise and this sparse equal-factor mechanism have different alphabets and costs. For k disjoint edges M=(3/2)^k, because the rank is twice a binomial(k,1/2). A public vertex cover of size k allows a competing classical search: fix its k variables, turn every gate into a linear equation and solve all 2^k cases. This can directly release after deciding the statement.

The rectangular interpolation retains shared k Boolean variables and l additional independent right-factor variables y. Its anchored rank-one set is (1,x)(1,x,y)^T. Compress duplicates to the constant, both sets of linear coordinates, all quadratic pairs of x and all x_i y_j. A uniformly chosen quadratic phase has form q(x)+L(x)+(Ax+b)·y. Summing over y yields 2^l times the sum over Ax=b, where A is a uniformly random l-by-k binary matrix. Conditional on rank t, b is consistent with probability 2^(t-l). On the affine solution space of dimension k-t, restricting a uniform degree-at-most-two polynomial again gives a uniform such polynomial: affine coordinates extend to an invertible ambient change, and every small polynomial extends. Therefore the inverse optimal common gain is exactly

    E_A [ 2^rank(A) M(K_{k-rank(A)}) ],

where K_d denotes the complete pair graph and M(K_0)=1. This interpolates full symmetry at l=0 and almost the unshared left-factor cost when A typically has full column rank. It allows arbitrary nonnegative probabilities and signed corrections at the issuer. It imposes flat positive signal on the full target; witness-computable nonconstant signs and circuit-dependent off-slice coefficients are expressly outside this optimum.

On a specific circuit after the independent syndrome mask, the odd Fourier series contains c exactly on valid feature vectors of accepting inputs and vanishes elsewhere. Orthogonality gives whole-transcript total variation at most c sqrt(number of accepting inputs), already at most c·2^64. For a unique accepting witness that upper bound is exact and the sign of its public parity is the optimal full-view test. On NO the complete laws coincide. In particular, unrestricted processing cannot amplify a single packet of this family beyond that upper bound. The formula also points to a possible escape: full circuit-specific cancellation/optimization can use every off-slice coefficient freely; merely conditioning rectangular factors to agree is fully accounted for above.

Executable finite control (standard Python 3). Compare literal full character sums against the interpolation, including the shared-variable corner. The cases use exponent at most 12 in the summation over coefficient masks.

```python
from fractions import Fraction
from itertools import combinations
def rank(xs):
    p = {}
    for x in xs:
        while x:
            i = x.bit_length()
            if i not in p:
                p[i] = x
                break
            x ^= p[i]
    return len(p)
def words(k,l):
    terms = list(combinations(range(k),2)) + [(i,k+j) for i in range(k) for j in range(l)]
    for x in range(1<<(k+l)):
        yield x + sum((((x>>i)&(x>>j)&1)<<(k+l+a)) for a,(i,j) in enumerate(terms))
def direct(k,l):
    ws = list(words(k,l))
    n = max(ws).bit_length()
    return Fraction(sum(abs(sum((-1)**((m&w).bit_count()%2) for w in ws))
                        for m in range(1<<n)),1<<n)
for k,l in [(1,0),(2,0),(3,0),(1,1),(2,1),(2,2),(3,1)]:
    rs = [rank([(a>>(k*j))% (1<<k) for j in range(l)]) for a in range(1<<(k*l))]
    assert direct(k,l) == sum((1<<r)*direct(k-r,0) for r in rs)/len(rs)
```


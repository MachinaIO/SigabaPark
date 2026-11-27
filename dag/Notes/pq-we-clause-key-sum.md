---
title: Exact binary key addition in a clause-restricted evaluator
refs: [note:pq-we-clause-subtree-rekey, note:pq-we-clause-restriction-spaces]
tags: [witness-encryption, reduction, correctness]
---

A public-key interface one might try in place of the clause evaluator oracle is to give one constrained key per clause, usable on traces satisfying that clause. Consider the following specific template. A common public setup independent of the clause contents defines F_K(x)=A_x K, with K in GF(2)^d, output in GF(2)^l, and public polynomial-time evaluation under chosen keys. A_x may be an arbitrary nonlinear function of x and of the setup. Its columns can be computed from unit keys. For bit zero sample clause keys whose sum is zero; for bit one sample independent uniform keys (so their sum is uniform). Give only their restrictions to their respective satisfying domains. At a witness the sum of evaluations is zero for bit zero and is nonzero for bit one with probability 1-2^(-rank A_x). This is the proposed decoder's completeness requirement. Exact binary key-linearity is stronger than the almost-homomorphism and single-key guarantees in [Brakerski and Vaikuntanathan](https://iacr.org/archive/tcc2015/90150001/90150001.pdf). The following calculation is about the template, not that construction.

**A false formula for the public interface.** For an n-bit word w, take n unit clauses fixing the bits to w and one wide clause that excludes only w. This formula is unsatisfiable. At w the units all authorize their outputs. The wide clause authorizes F_K(x) everywhere except w. Even treating its restricted key as a black box suffices to interpolate its output on most targets when d is polynomial and the address space is exponentially large. This statement allows fresh random setup *after* the target is fixed.

Draw M uniform n-bit training words and take w uniform and independent for the analysis. For any fixed setup let E(x) be the subspace spanned by the rows of A_x. Among any M+1 blocks at most d are essential, meaning their removal reduces the joint dimension. To see this choose one vector from each essential block outside the sum of the others. These vectors are independent by inspecting a nonzero coefficient in any putative dependence. By exchangeability,

    Pr[E(w) is not contained in the span of the training rows] <= d/(M+1).

This holds for each setup separately. With probability at most M/2^n a training word hits w; one may abort before making an unauthorized evaluation. On the remaining good event linear elimination of the public rows expresses every output bit of F_K(w) in terms of authorized evaluations. No extraction of K or access to the internals of the restricted key is required. Add the unit-clause outputs to recover the decoder's zero/nonzero statistic. On abort output zero. For the zero-message law the decoder always returns zero; for the one-message law its acceptance averaged over w is at least

    1 - E[2^(-rank A_w)] - d/(M+1) - M/2^n.

Here the uniform sum of keys is independent of the sampled words and setup (conditional on the setup). Thus some fixed false statement has at least this distinguishing gap over fresh setup and encryption randomness. For M=16d and nonzero A_w on all targets the bound is at least 1/2-1/16-M/2^n; if honest collision probability is negligible, the bound is correspondingly higher. The calculation needs 2^n much larger than M. No brute-force enumeration of the address space is involved. The conclusion assumes that restrictive keys supply the same common-family evaluations and the compiler does not first simplify this formula to a different representation.

**Boundary for a noisy proposal.** If the given oracle outputs are vectors whose *whole-vector* disagreement probability from their exact linear labels is at most eta on each authorized input, uniformly conditional on public setup and the chosen keys, the same argument loses at most (M+n)eta per message by a union bound. Small occasional failures of otherwise exact evaluations do not remove the obstruction. This does not bound interpolation of modularly rounded labels or group encodings without accessible field coordinates. A positive reduction for those models would need both correctness after adding all authorized outputs and a fixed-game argument for the joint information carried by the released keys. Merely invoking single-key off-domain pseudorandomness does not discharge either quantitative obligation.

The finite check enumerates every sequence of four input blocks for two public three-bit key families and verifies the essential-block bound. It also checks functional interpolation on every key whenever the held-out block is spanned, using only training outputs.
~~~python
from itertools import product
def feature_outputs(rows,key):
    return tuple((row&key).bit_count()%2 for row in rows)
def span(rows):
    s={0}
    for r in rows: s |= {x^r for x in s}
    return s
total=0
for family in (((1,2),(2,4),(3,5),(6,7)), ((0,0),(0,1),(2,2),(0,4))):
    for inputs in product(range(4),repeat=4):
        essential=0
        for i,x in enumerate(inputs):
            train=[r for j,y in enumerate(inputs) if i!=j for r in family[y]]
            if not set(family[x])<=span(train):
                essential+=1
                continue
            seen={}
            for key in range(8):
                obs=feature_outputs(train,key)
                val=feature_outputs(family[x],key)
                assert seen.setdefault(obs,val)==val
        assert essential<=3
        total+=1
print(total)
~~~

### Dithered modular rounding and the norm of an interpolation relation

For a concrete approximate variant take q=p h with odd step h>=3. The common public address map A(x) is one row over Z/q, and raw phase s_i(x)=A(x)K_i. Give clause i an independent public dither D_i uniform in {0,...,h-1} sampled after the keys. Its authorized evaluation transmits the index modulo p of the nearest multiple of h to s_i(x)+D_i. Locally lift the index by multiplying by h and subtracting D_i modulo q. This yields s_i(x)+e_i(x), where the centered integer error is uniform from -(h-1)/2 through (h-1)/2 for each fixed x and keys. Errors at the same x are independent across clauses; errors at different x under the same key need not be independent. These are probability statements over setup for a fixed input or witness.

On a witness add all m lifted values and test if the centered distance from zero is at most T=(h-1)sqrt(m ln(2/eta)/2). Hoeffding gives a tail probability at most eta for the sum error. The zero-sum branch accepts with probability at least 1-eta. In the independent-key branch assume A(x) is primitive modulo q (its entries and q generate the unit ideal); then the actual sum phase is uniform mod q. Acceptance implies that this phase is within 2T of zero unless the error tail occurs. Thus acceptance is at most eta+min(1,(4T+1)/q). In particular for fixed eta the rounding alphabet need only scale as a sufficiently large constant times sqrt(m) for constant-gap witness recovery. With independent encryptions this correctness gap can be amplified by majority when both conditional errors are below 1/2. The analysis does not construct a restricted key or prove false-instance security.

**False-instance constraint.** Use the preceding n unit clauses fixing w and the one clause excluding w, so m=n+1. Suppose a public relation A(w)=sum_j c_j A(x_j) modulo q with x_j!=w is available using polynomially many signed integer coefficients with L=sum_j |c_j|. Apply it to the wide clause's authorized lifted values, and add the other m-1 authorized outputs at w. The resulting phase error has magnitude at most

    B = (h-1) (sqrt((m-1) ln(2/eta)/2) + L/2)

except with probability eta. Only the first m-1 clause errors use concentration. The wide clause's correlated errors are bounded by the triangle inequality, so the calculation does not assume fresh dithers for different inputs. Use a centered threshold B to distinguish. If A(w) is primitive, the zero-branch versus independent-branch acceptance gap is at least 1-2 eta-min(1,(4B+1)/q), by the same implication about the uniform true phase. The relation and evaluation points should be fixed before sampling the dithers, e.g. obtained from the public feature map alone.

A concrete source of short relations is a feature map whose coordinates are multilinear polynomials of degree <=s in the n Boolean inputs *over Z/q*, with s<n. On any (s+1)-dimensional coordinate subcube through w the alternating sum of every column vanishes: each monomial omits at least one toggled variable. Isolate the corner w to get L=2^(s+1)-1 and coefficients all plus or minus one. The proof works for arbitrary w, composite q and fresh coefficients of this bounded degree. It is efficient for s=O(log n). It does not apply merely because a feature map can be evaluated by a small Boolean circuit, nor does it establish anything about the full BV constrained-key construction. The quantitative design requirement is to rule out useful *short, efficiently available* relations at the same rounding parameters as honest recovery. A large modular interpolation coefficient is different from a small signed one. Ruling out these relations would still be only a necessary screen, not a reduction to LWE.

The listing checks the relation and the deterministic bound for every quadratic polynomial on three bits modulo three lifted to integer coefficients, at all eight target corners modulo 15. It separately exhausts all phases and dithers for the exact error law and evaluates one illustrative analytical bound.
~~~python
from collections import Counter
from itertools import product
from math import log,sqrt
q,h=15,5
def error(v,d):
    return ((v+d+h//2)//h)*h-d-v
for v in range(q):
    assert Counter(error(v,d) for d in range(h))==Counter(range(-h//2+1,h//2+1))
monomials=[v for v in range(8) if v.bit_count()<=2]
for coeff in product(range(3),repeat=len(monomials)):
    phases=[sum(c for c,v in zip(coeff,monomials) if x&v==v)%q for x in range(8)]
    for w in range(8):
        terms=[(x,(-1)**((x^w).bit_count()+1)) for x in range(8) if x!=w]
        assert (sum(c*phases[x] for x,c in terms)-phases[w])%q==0
        d=w%h
        assert abs(sum(c*error(phases[x],d) for x,c in terms))<=7*(h//2)
m,p,h,eta,L=4097,2048,257,1/32,15
T=(h-1)*sqrt(m*log(2/eta)/2)
B=(h-1)*(sqrt((m-1)*log(2/eta)/2)+L/2)
print("honest one-branch error bound",eta+(4*T+1)/(p*h))
print("false distinguishing gap bound",1-2*eta-(4*B+1)/(p*h))
~~~

---
title: Full-root rank survival for the tensor WE correctness budget
refs: [definition:WE_CircuitSAT, note:pq-we-ordered-radix-gadget, note:pq-we-self-consistent-modulus, note:pq-we-packed-columns]
tags: [witness-encryption, correctness, complexity]
---

A valid nonzero message needs just one surviving tensor row. When multiple root rows are sent, failure requires all of them to disappear or the surviving terminal signal to look short. The rows share the same later matrices; their extinction events cannot be multiplied as independent. Here we propagate the rank of their joint product. The result concerns one fixed valid witness in the earlier correctness setting, with independent factor entries and independent factors across its selected levels. This does not bound failure simultaneously for paths an observer selects after seeing the coins.

**Rank transition.** Work over F_p, where q is a power of p. Let rho upper-bound every atom of every tensor-factor entry modulo p. Start with d selected standard rows, 1 <= d <= n. Given the current product P of rank r, form the next product P S one column at a time. If the previous output columns span W of dimension k, the new column falls in W only when its independent input vector lies in the preimage of W, of codimension r-k. After fixing the coordinates outside a pivot set of size r-k, each pivot value is determined. The probability of a miss is at most rho^(r-k). The different rows of P S need not be independent.

Model a pessimistic rank by starting at zero and taking n trials, where state k stays put with probability rho^(r-k) and otherwise increments. Each accumulator rank increases by at most one per trial. With the same uniform coin, the true rank dominates the model: at equal states its conditional miss probability is no larger, and at unequal states the smaller cannot overtake in one trial. The model is monotone in r by the same coupling. Its rank-transition rows can therefore be composed for H independent factors, starting at d. The resulting probability of rank zero is an upper bound even when the actual transitions depend on the full previous product. Evaluating this finite recursion with exact rationals gives a certificate. For the dyadic upper bound 1/2 this has polynomial bit complexity in n and H: transition probabilities have a common denominator dividing 2^(n²), so after H stages O(Hn²) denominator bits suffice.

**Implemented atom bound.** For p=7 the exact clocked center-zero scalar sampler at width two and per-draw precision five admits rho=1/2. Enumerate both sides and offsets in every retained shell, using the actual integer acceptance threshold. The conditional law of a successful trial is its joint accepted residue mass divided by the total acceptance acc. Timeout adds at most (1-acc)^K to any residue; acc>=1/8 implies this is at most 2^(-floor(K/8)). Rational evaluation gives an upper bound below 1/2 (approximately 0.4999971390). The support cap is at most 7, hence the previous S=8 cap covers it. This calculation specifies concrete independent sampler coins and does not infer cryptographic security or high statistical fidelity to an ideal sampler from correctness. Other precisions, primes or entry distributions require their own atom bound.

**Final test.** If the product modulo p survives, at least one coefficient is a unit modulo q. Tensoring with a valid logical message-one row containing a unit preserves this property. Pick the first such row using only the plaintext factors and the fixed witness. For an independent uniform terminal matrix, each of its t retained columns maps to an independent uniform residue in that row. Testing all retained rows for smallness implies that each of those t ideal residues lies in a centered interval of at most 4B+1 elements even if encryption noise is correlated. Thus failure probability is bounded by the modeled extinction probability plus ((4B+1)/q)^t plus the statistical distance of the terminal public matrix from uniform. The latter is at most 2^(-key_bits). Message zero passes the shortness test on every outcome by the previous residual bound. Deleting unused root rows and final columns is deterministic ciphertext postprocessing for fixed public d and t. All intermediate matrices are still transmitted in full. Honest algorithms may omit the corresponding unused outputs, preserving their marginal law with independent column sampler coins.

**Accounting.** For H=8, w=6, p=7, target failure below 2^-32, S=8, and E=16, the previous single-row sufficient dimension was 592. Its best full-root packed payload in the previous radix search was 579646206906272 bits. At n=9 the new full-rank extinction bound is about 1.204e-10. With all terminal columns kept, the best full-root payload becomes 68122045920 bits. Retaining 13 terminal columns and all nine root rows gives 58407566376 bits, 185906 sampled columns and 12958577730 scalar multiply-adds in the selected matrix chain. The prime power is 7^81, radix 16, and m=15490. At n=10, keeping six root rows and 16 terminal columns instead gives 74027670088 bits and 11487552336 multiply-adds: smaller decryption work at a larger payload. These are operation and payload accounts per message bit. No encryption at these dimensions has been timed. The new dimensions meet a correctness target. Any lattice-hardness or security-reduction dimension floor is independent and must also be applied. Exact enumeration of the product law of binary 2-by-2 matrices verified the upper bound through four factors at three distinct biases, with equality at uniform input.

The following code uses threshold from the clocked scalar sampler, select from the ordered radix planner, and layout from the packed-column note. The tuple returned by budget contains payload bits, radix exponent, modulus exponent, matrix width, retained root rows, retained terminal columns, number of sampled columns and dense decryption multiply-adds. The search minimizes payload over the tested radix range at a supplied dimension; it reuses the conservative full-size preimage precision and modulus certificate.

~~~python
from fractions import Fraction as F

def rank_rows(n,rho):
    rows=[]
    for r in range(n+1):
        law=[F(1)]+[F(0)]*r
        for _ in range(n):
            new=[F(0)]*(r+1)
            for k,prob in enumerate(law):
                miss=rho**(r-k)
                new[k]+=prob*miss
                if k<r:
                    new[k+1]+=prob*(1-miss)
            law=new
        rows.append(law)
    return rows

def extinction(n,H,rho):
    rows=rank_rows(n,rho)
    # Bound for every possible matrix of each rank, with zero remaining steps.
    bad=[F(1)]+[F(0)]*n
    for _ in range(H):
        assert all(x>=y for x,y in zip(bad,bad[1:]))
        bad=[sum(p*e for p,e in zip(row,bad)) for row in rows]
    return bad[n]
from fractions import Fraction as F
from math import isqrt

def scalar_atom(pmod,b,threshold):
    # Center zero, width two; exactly the same decisions as sample_squared.
    t=isqrt((b+12)//4)+1
    K=256*(b+2)
    p=b+K.bit_length()+4
    joint=[F(0)]*pmod
    for r in range(t):
        for i in range(2):
            for j in (-2*r-i,1+2*r+i):
                a=min(1<<p,threshold(F(j*j,4),p+r))
                joint[j%pmod]+=F(a,1<<(r+p+3))
    acc=sum(joint)
    # Exact conditional success law, adding a small rational upper bound on timeout.
    assert acc>=F(1,8)
    return max(joint)/acc+F(1,2)**(K//8)
def budget(H,w,n,p,lam,S,E,rho,select,layout):
    if H<2:
        raise ValueError("requires separate root and final blocks")
    rows=rank_rows(n,rho)
    bad=[F(1)]+[F(0)]*n
    for _ in range(H):
        bad=[sum(x*y for x,y in zip(row,bad)) for row in rows]
    key_bits=lam+(H-1).bit_length()+3
    best=None
    for a in range(1,17):
        j,q,c=select(H,w,n,p,lam,S,E,a)
        m=c['m']
        cap=layout(m,q,c['C'])[0]
        box=F(4*c['B']+1,q)
        for d in range(1,n+1):
            slack=F(1,2**lam)-bad[d]-F(1,2**key_bits)
            if slack<=0:
                continue
            t=1
            while t<=m and box**t>=slack:
                t+=1
            if t>m:
                continue
            columns=2*((H-2)*m+t)
            payload=2*d*m*c['k']+columns*cap
            result=(payload,a,j,m,d,t,columns,d*((H-2)*m*m+m*t))
            if best is None or result<best:
                best=result
    return best
~~~

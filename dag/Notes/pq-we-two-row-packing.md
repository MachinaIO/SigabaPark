---
title: Packing messages into two-row moment blocks with pilot columns
refs: [note:pq-we-rank-coded-shifts, note:pq-we-private-moment-products, note:pq-we-rectangular-gate-moments]
tags: [witness-encryption, correctness, coding, complexity]
---

The square rank-code construction pays for perfect correction of every rank-one error. For moment encryption the error is random with a shared left factor. This permits two rows and a growing number of columns while retaining polynomial-time witness decoding and a tunable failure bound.

**Reason to keep two rows.** A normalized false-instance moment of rank r yields a projected unshifted b-by-b matrix of rank at most r. For a full-rank shift Z and b>r, the shifted projection has full rank except with probability at most min(1,2b/q). Indeed its determinant is a polynomial of degree at most 2b in the independent uniform private factor entries. Its constant term is det Z, so the Schwartz-Zippel bound applies. Thus the two projection laws have distance at least max(0,1-2b/q). Multiplication by a nonzero field element in the previous square code supplies full-rank message differences. This is a limitation on increasing b for that candidate at large q. In contrast a single normalized rank-r projection with two rows and r>=2 is exactly uniform conditional on the two projected left rows being independent, even if it has many columns. The probability of dependence is 1-(1-q^(-r))(1-q^(1-r)). This bounds the marginal distance between any two shifts by coupling the full-row-rank part. It does not bound the joint view across moments.

**Encoding.** Fix s>=2 and a representation of F_(q^s) with alpha outside F_q. Use blocks of size 2 by s+p with p>=1. Draw L,R as in the private moment construction with these sizes. Encode m in F_(q^s) by the translation Z_m whose first p columns are zero and whose last s columns are the coordinate rows of (m,alpha m). Encrypt with blocks L K_i R^T+gamma_i Z_m. On a valid trace the linear combination gives Z_m+u v^T, where u and v are independent uniform vectors of lengths 2 and s+p, since both anchored trace vectors are nonzero. The p pilot columns contain u times the first p coordinates of v. If a pilot is nonzero, choose a nonzero row (a,b) annihilating it. Apply this row to the s data columns; the extension-field element obtained is (a+b alpha)m. It has a nonzero multiplier by the choice of alpha. Recover m by one division. If all pilots are zero, accept the first data row as the message when the second equals alpha times the first, otherwise return an erasure. In that fallback a nonzero rank-one error cannot turn one data codeword into another because every nonzero codeword difference has row rank two. Thus an honest run either recovers m exactly or gives a detectable erasure. The exact erasure probability is

    (1-q^(-2)) q^(-p) (1-q^(-s)).

The three factors are respectively nonzero u, all pilot entries of v zero, and nonzero data entries of v. For standard fixed-length Dec one may map erasure to an arbitrary message, bounding its error by this probability. There is no discrete logarithm, enumeration of field elements, or search for the secret. All operations are polynomial with a supplied field representation. The scheme uses 2h(s+p) field elements for s payload elements for h moment basis matrices. With s=8,p=1 this is 18h for eight payload symbols versus 16h in the preceding 4-by-4 perfectly correcting format, while using only two left rows. With q>2^lambda, one pilot suffices for error below 2^-lambda. At smaller q, taking p=ceil(lambda/log2 q) suffices.

**Security obligation.** Translations form an additive subspace supported on the data columns, so the previous factor-two, single-call wrapper applies at the new dimensions. For a fixed falsifiable game to yield general CircuitSAT security it must simulate the *entire* false-instance view, including pilots of every block with their shared private factors. The single-projection bound above, or a proof for a transcript without pilots, cannot be substituted. This is a correctness and dimensional tradeoff, without a general hiding claim.

**Exact check.** The example uses F_9=F_3[alpha]/(alpha²+1) with s=2 and p=1. Multiplication by alpha sends (x,y) to (-y,x). Count every erasure and verify every non-erased message.
~~~python
from itertools import product
q=3
F=list(product(range(q),repeat=2))
def alpha(x):
    return (-x[1]%q,x[0])
def scale_sum(a,x,b,y):
    return tuple((a*u+b*v)%q for u,v in zip(x,y))
def decode(rows):
    (p0,*x),(p1,*y)=rows
    if not (p0 or p1):
        return tuple(x) if alpha(x)==tuple(y) else None
    a,b=p1,-p0
    w=scale_sum(a,x,b,y)
    # Invert a+b alpha using its conjugate and the norm.
    inv=pow((a*a+b*b)%q,-1,q)
    return scale_sum(inv*a,w,-inv*b,alpha(w))
bad=total=0
for m,u,v in product(F,F,product(range(q),repeat=3)):
    z=((0,*m),(0,*alpha(m)))
    rows=[[(c+ui*vj)%q for c,vj in zip(row,v)] for row,ui in zip(z,u)]
    result=decode(rows)
    assert result is None or result==m
    bad+=result is None
    total+=1
assert bad*q**5==total*(q**2-1)*(q**2-1)
print(total,bad,total-bad)
~~~

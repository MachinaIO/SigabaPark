---
title: Exact two-mode hiding criterion with shared bilinear and gate masks
refs: [note:pq-we-gate-moment-noise, note:pq-we-new-directions]
tags: [witness-encryption, reduction, correctness, complexity]
---

Keep the previous moment matrices E_i and gate test matrix Q. For a fixed public t-by-d S let H_S send r to the column array with columns S E_i r. Let W_S be the image of H_S plus the space of arrays with each row in rowspace(Q). Write Z for the t-dimensional space of arrays supported on column 00. Use uniform field masks r,B in both modes. Encrypt zero as H_S(r)+B Q and one by adding an independent uniform element of Z to the same law. This uses only t(d+k) field elements including S. No small error or secret search is needed for this experiment.

For a satisfying trace x let a be its moment vector. Then Ya=(Sx)(x^T r) in mode zero. The 00 entry of a is one, so in mode one Ya is uniformly distributed over t field elements conditional on S. Decode zero exactly when Ya lies in the span of Sx. Zero-mode decoding is exact; one-mode error is at most q^(1-t), including when Sx=0. All procedures are polynomial for polynomial dimensions and log q.

**Compute the missing directions, not the ambient deficit.** Conditional on S the laws are exactly uniform on W_S and W_S+Z. For c(S)=dim(W_S+Z)-dim(W_S) their total variation is exactly 1-q^(-c(S)). The unconditional distance including the public S is the average of this expression. Membership in W_S attains the distance using field elimination. Thus replacing independent uniform output by the shared-mask comparison repairs the earlier support defect precisely when Z is absorbed with overwhelming probability. An ambient dimension deficit alone does not decide this criterion.

It suffices to compute ranks in the unmasked coordinates. Let A have as columns any basis for the right kernel of Q. The map Y -> YA has kernel exactly the gate-mask space. Set H to be the matrix of r -> H_S(r)A after flattening, and gamma the 00 row of A. Set J to the matrix with one copy of gamma in each corresponding row block (mapping t scalars to those blocks). Then c(S)=rank([H J])-rank(H). This includes absorption by the correlated bilinear term even when gamma is nonzero; checking only membership of the constant in the gate span would miss that possibility. For example, in an abstract quotient with a single surviving coordinate, gamma=1 and H surjective, the gate span alone does not hide the shift while the combined masks do.

**A positive rank promise.** If ker(Q) has exactly one generator a and a_00 is nonzero, then J spans the whole t-coordinate quotient. Put rho=rank(sum_i a_i E_i). The projected matrix H is just S times that pencil element. For uniform S its rank is distributed as the rank of a uniform t-by-rho matrix, by an invertible basis change. For rho>=t the probability of exact absorption is the product over j=0,...,t-1 of (1-q^(j-rho)). Consequently the unconditional distance is at most (q^t-1)q^(-rho)/(q-1), by a union bound over lines in the left kernel. For t=2 the honest error is at most 1/q while this NO bound is (q+1)q^(-rho). This gives simultaneous polynomial costs and statistical hiding on this restricted promise using no computational assumption. It does not classify arbitrary circuits: the three-gate example has a seven-dimensional kernel. The kernel and rank conditions themselves are decidable by elimination.

**Test on the identically false circuit from the previous note.** Over F_5 with two public rows, the listing prices the exact conditional distance for each of 200 seeded choices of S. The codimension is two in 196 trials and one in four, giving conditional distances 24/25 and 4/5 respectively. It also exhausts all masks for a one-coordinate quotient to check the distance formula independently. These are algebraic controls. No fixed hardness game is invoked. Since nonabsorption is publicly detectable, a computational reduction cannot rescue this particular linear comparison law on instances where nonabsorption is frequent. To retain this comparison while seeking computational hiding, a new construction must change the joint laws themselves. Sampling uniform linear masks more efficiently or renaming their generating problem does not alter the criterion.

~~~python
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement,product
from random import Random

def basis(rows,q):
    pivots={}
    for row in rows:
        v=[x%q for x in row]
        for j in sorted(pivots):
            c=v[j]
            v=[(a-c*b)%q for a,b in zip(v,pivots[j])]
        if any(v):
            j=next(i for i,x in enumerate(v) if x)
            pivots[j]=[x*pow(v[j],-1,q)%q for x in v]
    return pivots

q,d,t=5,5,2
pairs=list(combinations_with_replacement(range(d),2))
k=len(pairs)
def vector(terms):
    v=[0]*k
    for i,j,c in terms:
        v[pairs.index(tuple(sorted((i,j))))]+=c
    return v
Q=[vector([(j,j,1),(0,j,-1)]) for j in range(1,d)]
for u,v,z in [(1,1,2),(1,2,3),(3,3,4)]:
    Q.append(vector([(0,z,1),(u,v,1),(0,0,-1)]))
Q.append(vector([(0,4,1),(0,0,-1)]))
def embed(row,i):
    return [0]*(k*i)+row+[0]*(k*(t-i-1))
gate=[embed(row,i) for row in Q for i in range(t)]
shift=[embed([1]+[0]*(k-1),i) for i in range(t)]
counts=Counter()
rng=Random(317)
for trial in range(200):
    S=[[rng.randrange(q) for j in range(d)] for i in range(t)]
    images=[[s[i]*(j==v)+(s[j]*(i==v) if i!=j else 0)
             for s in S for i,j in pairs] for v in range(d)]
    c=len(basis(gate+images+shift,q))-len(basis(gate+images,q))
    counts[c]+=1
print("conditional codimensions",dict(counts))
for h in [(0,0),(1,0),(1,2)]:
    R=Counter(tuple(v*x%q for v in h) for x in range(q))
    U=Counter(product(range(q),repeat=2))
    tv=sum(abs(Fraction(R[y],q)-Fraction(U[y],q*q)) for y in U)/2
    assert tv==1-Fraction(1,q**(2-int(any(h))))
~~~

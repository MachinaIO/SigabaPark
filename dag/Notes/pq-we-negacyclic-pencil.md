---
title: A fixed ring challenge for non-peelable pencils and a norm bound on rank-one witnesses
refs: [definition:WE_CircuitSAT, note:pq-we-rank-pencil-peeling, note:pq-we-short-rank-pencil]
tags: [witness-encryption, reduction, correctness, rank]
---

Let d be a power of two, q an odd prime and H_j the signed permutation matrix satisfying s^T H_j r = [x^j](sr mod (x^d+1)). For k>=2 distinct output positions j, none of these matrices has a private coordinate. Consider a pencil of the form M_i=L H_(j_i) P where L is invertible modulo q and P is a signed permutation. Assume a symmetric iid short coefficient secret law and iid coefficient errors. Use the fixed decisional short-secret Ring-LWE game on this ring at t samples with exactly those laws and the required quantum hardness. The classical challenger samples a hidden bit, uniform public multipliers and either noisy products or uniform ring responses. The ring, laws and dimensions can be fixed by the size class. The broad Ring-LWE framework is described by [Lyubashevsky, Peikert and Regev](https://cims.nyu.edu/~regev/papers/ideal-lwe.pdf); a worst-case theorem for these exact secret/error parameters is not being invoked.

Given the orbit description, let A contain the coefficient rows of the t public multipliers. Output S=A L^-1 and select the indicated coefficients of each response as Y. In the real game the single hidden ring secret has exactly the law of P r. This gives all columns S M_i r plus the right independent errors, including their correlations given S. Uniform responses project to independent uniform columns. Thus the real/uniform gap transfers in one challenge without advantage loss. Encryption need only use the statement matrices. A fixed-statement reduction can take a verified orbit description as advice; uniform reduction time must include obtaining it. With a supplied description honest real-mode evaluation can likewise use t polynomial products rather than k unrelated dense matrix products per public row. This is a reduction on a restricted family of statements. There is no suggestion to give the challenger a circuit or to assume a WE primitive.

**What happens to rank-one coefficients.** Write a for a signed integer lift of the combination coefficients, padded with zeros at unselected positions. In the ring over the integers set g=a_0-sum_(j=1..d-1) a_j x^(d-j). The constant coefficient of g(sr) modulo x^d+1 is the desired linear functional on sr. The bilinear matrix of this pairing is H_0 times the multiplication matrix of g. Thus the modular rank rho of the combination equals the rank of multiplication by g modulo q, since H_0,L,P are invertible. For a nonzero residue vector a, g is a nonzero element of the rational cyclotomic field. Its integer multiplication matrix therefore has nonzero determinant. Reduction modulo q has nullity d-rho, so at least d-rho integer Smith factors are divisible by q. Every column is a signed permutation of g's coefficient vector, with Euclidean norm ||a||_2. Hadamard's bound gives

    q^(d-rho) <= |det(mult_g)| <= ||a||_2^d.

In particular a rank-one coefficient vector must have norm at least q^(1-1/d), even under the allowed changes of basis. Rank one is possible algebraically: when x^d+1 splits, evaluation at a root alpha has coefficients a_j=alpha^j and gives the outer product of the evaluation vector with itself. Taking d=4, q=17, alpha=2 already illustrates this distinction. For q<=2^d, rank one forces ||a||_1 >= q/2. With entrywise error cap E>=1 the previous correctness certificate D=E||a||_1 cannot certify 2D+1<=q. This rules out that certificate, not every possible decoder. More generally an orbit with a short polynomial description checkable by matrix identities still gives a short NO certificate if every valid YES witness must meet the incompatible cap in this regime. It therefore cannot by itself certify all false CircuitSAT instances unless NP=coNP. The local algebraic rank obstruction from coordinate peeling has been replaced by a quantitative obstruction on the decoding witness.

**Exact controls.** Check the coefficient identity for all basis triples, then exhaust every pencil coefficient vector over the smaller ring with d=4, q=5. Compute determinant by the integer Leibniz formula and rank by field elimination; also check the rank-one example over 17.
~~~python
from itertools import permutations, product
from math import prod

def matrix(a):
    d=len(a)
    return [[(1 if i+j<d else -1)*a[(i+j)%d] for j in range(d)] for i in range(d)]

def rank(A,q):
    rows=[r[:] for r in A]
    lead=0
    for j in range(len(A[0])):
        i=next((i for i in range(lead,len(A)) if rows[i][j]%q),None)
        if i is None:
            continue
        rows[lead],rows[i]=rows[i],rows[lead]
        pivot=rows[lead]
        for i in range(lead+1,len(A)):
            c=rows[i][j]*pow(pivot[j]%q,-1,q)
            rows[i]=[(x-c*y)%q for x,y in zip(rows[i],pivot)]
        lead+=1
    return lead

d=4
for i,j,k in product(range(d),repeat=3):
    basis=[int(l==k) for l in range(d)]
    assert matrix(basis)[i][j]==(1 if i+j<d else -1)*int((i+j)%d==k)
for a in product(range(-2,3),repeat=d):
    if not any(a):
        continue
    A=matrix(a)
    det=sum((-1)**sum(p[i]>p[j] for i in range(d) for j in range(i+1,d))
            *prod(A[i][p[i]] for i in range(d)) for p in permutations(range(d)))
    divisor=5**(d-rank(A,5))
    assert det and det%divisor==0 and det**2<=sum(x*x for x in a)**d
assert rank(matrix([1,2,4,8]),17)==1
print("624 determinant checks and the split-prime rank-one example passed")
~~~

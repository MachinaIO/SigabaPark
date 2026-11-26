---
title: Short shared randomness and a fixed matrix-LWE hybrid for rank pencils
refs: [definition:WE_CircuitSAT, note:pq-we-fixed-rank-pencil, note:pq-we-rank-gap-lattice-barriers]
tags: [witness-encryption, reduction, rank, complexity]
---

Fix a prime q and public integer d-by-d matrices M_1,...,M_k. Write V(r) for the d-by-k matrix of columns M_i r. Use independent short coordinates in r modulo q, each with maximum point probability p. Draw a uniform h-by-d matrix C. If every nonzero pencil combination over F_q has rank at least R, then

    TV((C,C V(r)), (C,U)) <= (1/2) sqrt((q^(hk)-1) p^R).

Here U is independently uniform h-by-k. In particular all rows use the SAME short vector. For each fixed C, expand the chi-squared divergence from uniform by additive characters of the output. The squared modulus at a nontrivial character indexed by an h-by-k array is an expectation over independent r,r'. Averaging over the rows of C gives the probability that for every row of coefficients a, M(a)(r-r')=0. At least one a is nonzero. Fix r' and all nonpivot entries of r for that matrix. The R pivot coordinates must take prescribed values, with joint probability at most p^R. Sum over nontrivial characters, use Cauchy-Schwarz for TV, and then Jensen. This identity also allows exact evaluation using stacked ranks for uniform field inputs.

**Fixed-game embedding.** For one encrypted bit send (S,Y), with uniform t-by-d matrix S. In mode zero set Y=S V(r)+F and in mode one draw independent uniform Y. All arithmetic in the ciphertext is modulo q. Take F iid uniform integer flooding entries from [-G,G]. The fixed decisional LWE game has uniform public B of shape t-by-h and response Bz+e (or uniform), with fresh uniform z and entrywise errors bounded by E. Dimensions and error laws are fixed public size parameters shared across statements; pad within the size class. The reduction can sample r,F and compute the public M_i on its own. A column hybrid replaces S by B C+E_S at cost d times the single-secret advantage. Jointly with B,C,r and the challenge sampling coins except F, translating F by E_S V(r) costs at most tk E L/(2G+1), for L a uniform bound on the maximum column 1-norm of the integer V(r). This follows by coupling translated intervals and taking a union bound. The resulting joint view is (B C+E_S,B C V(r)+F). Replace C V(r) by U using the preceding inequality, retaining C for simulation. Introduce a new independent LWE error E_Y in the second component by the same interval coupling at cost tk E/(2G+1). Replacing all d+k columns of [B C+E_S | B U+E_Y] by uniform and adding F on the right gives mode one. Thus the difference of acceptance probabilities is at most

    (2d+k) Adv_LWE + tk E (L+1)/(2G+1) + (1/2) sqrt((q^(hk)-1) p^R).

Charge matrix formation, flooding and other ciphertext work to the reductions' running times. Classical challenges and a one-call wrapper preserve the quantum distinguisher model. Unbounded LWE noise requires also charging the probability that entries exceed E. Uniform intervals can be sampled to bounded precision with the sampler error included.

**Witness decoding.** A witness provides nonzero a modulo q with a short signed lift, M(a)=u v^T modulo q and a publicly polynomial-size list containing the possible c=v^T r. In mode zero Ya-cSu=Fa for the correct c, with centered infinity norm at most D=G ||a||_1. Return zero if any listed c passes this test. In mode one Ya is uniform conditional on S, so its false acceptance probability is at most list_size times ((2D+1)/q)^t when 2D+1<=q. This explicitly exposes the tension between flooding precision, modulus, LWE hardness, and the length of a. Polynomial matrix dimensions, log q, witness processing and list length give polynomial honest costs. No obfuscation primitive occurs.

**Scope of the sufficient condition.** This establishes a reduction for a rank promise with the displayed parameters. It does not supply a general CircuitSAT compiler. In fact the sufficient extractor condition itself already implies statistical hiding for the clear scalar construction using any number of public rows up to h. If its witness test achieves completeness and negligible false acceptance at such a row count, a polynomial reduction from all CircuitSAT to that promise would give statistical WE and put NP in SZK. For a general construction the open step is a computational comparison *after multiplication by the hidden B*, in parameter regimes where statistical extraction of the entire C V(r) is unavailable. Merely postulating that comparison for each NO statement would reintroduce the prohibited statement-dependent premise. Uniform large-modulus LWE with the required advantage is a separate parameter assumption.

The following exact check compares the average chi-squared divergence with the character sum for a shared binary r over F_3, in a full-rank pencil and a pencil with a rank-one member.
~~~python
from collections import Counter
from fractions import Fraction
from itertools import product
q = 3
vectors = list(product(range(q),repeat=2))
short = list(product(range(2),repeat=2))
def dot(x,y):
    return sum(a*b for a,b in zip(x,y)) % q
for transform,R in ((lambda x:(-x[1],x[0]),2),(lambda x:(x[0],0),1)):
    for h in (1,2):
        total = 0
        characters = list(product(vectors,repeat=h))
        for C in characters:
            hist = Counter(tuple((dot(c,r),dot(c,transform(r))) for c in C) for r in short)
            total += q**(2*h)*sum(n*n for n in hist.values())-len(short)**2
        direct = Fraction(total,len(characters)*len(short)**2)
        count = 0
        for A in characters:
            if not any(any(row) for row in A):
                continue
            for r,s in product(short,repeat=2):
                v = tuple(x-y for x,y in zip(r,s))
                w = transform(v)
                count += all((a*x+b*y)%q==0 for a,b in A for x,y in zip(v,w))
        assert direct == Fraction(count,len(short)**2)
        assert direct <= Fraction(q**(2*h)-1,2**R)
        print(R,h,direct)
~~~

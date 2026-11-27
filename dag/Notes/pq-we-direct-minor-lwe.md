---
title: An exact short-secret LWE reduction for a rank-pencil promise
refs: [definition:WE_CircuitSAT, note:pq-we-short-rank-pencil]
tags: [witness-encryption, reduction, rank, complexity]
---

**A one-challenge simulation.** Fix prime q, dimensions d,k,t,h with h>=2 and kh<=d, an efficiently samplable short iid secret law and an efficient error law. These parameters depend only on the public size class. Given d-by-d matrices M_i, draw uniform S with t rows and a fresh short vector r of length d. Encrypt zero as (S,Y) with column i of Y equal to S M_i r + e_i for independent error entries. Encrypt one with independent uniform Y. The single fixed decisional game gives a uniform tk-by-h design and one response column, either its product with a fresh short h-vector plus the same errors or uniform. The challenger can sample both experiments and score a hidden-bit guess efficiently. Quantum hardness at the specified parameters is a hypothesis. No general conversion from uniform-secret LWE parameters is presumed.

Suppose some h-element coordinate set J makes the d-by-kh concatenation P=[M_1[:,J] | ... | M_k[:,J]] full column rank. Reorder challenge rows to form a uniform t-by-kh matrix B of k adjacent t-by-h blocks, preserving the correspondence with its response entries. With a left inverse D of P and an independent uniform t-by-d matrix W, put

    S = B D + W (I - P D).

Then SP=B. For fixed B the expression samples the entire affine fiber uniformly, since multiplication by I-PD maps onto the left kernel of P and fixes that kernel pointwise. Consequently S is uniform marginally. Sample r outside J independently and give each response entry the known offset from those coordinates under S M_i. The real game now gives the exact zero law with the single challenge secret shared on J. The uniform game gives the exact one law. The advantage factor is one, plus polynomial simulation time and any cost to obtain J. For fixed-statement nonuniform reductions J costs O(h log d) advice bits. A uniform reduction needs a finder when J is not supplied. Encryption and valid-witness decryption do not use J. There is no flooding or statistical extraction step. This directly embeds a fixed, falsifiable problem even when short secrets have too little entropy to make the full transcript statistically uniform.

**Correctness and size.** Use the preceding note's rank-one witness M(a)=u v^T, nonzero a, short lift of a, and polynomial-size list containing v^T r. If error entries have absolute value at most E except with total probability delta, use D_err=E ||a||_1. The zero-mode failure probability is at most delta and the one-mode failure probability is at most list_size ((2D_err+1)/q)^t for 2D_err+1<=q. Send t(d+k) field elements per bit. Dense encryption takes O(k d² + tkd) field operations and polynomial sampling work. Decoding forms Ya and Su in O(t(k+d)) field operations and checks the list in O(t list_size) further operations, in addition to witness conversion. These are symbolic guarantees for parameters meeting the bounds and the fixed-game hardness hypothesis.

**Why a global minor cannot cover all of CircuitSAT.** For every nonzero coefficient vector a the columns of M(a) restricted to J are independent: a relation with coefficient vector z would give P applied to the block vector (a_i z)_i equal to zero, forcing z=0. In particular rank M(a)>=h. Thus a valid minor and any rank-one YES witness are mutually exclusive. For an efficiently compiled family of polynomial dimensions, J is an NP certificate checkable by field elimination for the proposed NO promise. If every unsatisfiable circuit compiled to such a pencil and every satisfiable one admitted a rank-one witness, UNSAT would be in NP. This implication is independent of whether J can be found efficiently. A certificate even for a freely chosen short subspace basis in place of coordinate columns faces the same obstruction. A general reduction using this simulation must therefore change its role, for example by handling individual rejecting witness branches while accounting for their combined reduction loss and hiding their shared ciphertext correlations. The local simulation here gives no such composition theorem.

**Exact arithmetic check.** This example has a non-coordinate image for the second generator and a nonempty kernel. The check compares the two complete ciphertext histograms for a nonuniform-size binary secret inside F_3 and verifies the uniform challenge and fiber law. Small parameters serve only to check distributions.
~~~python
from collections import Counter
from itertools import product

q = 3
# d=5, k=h=2, t=1, J=(0,1). SP=(s0,s1,s2+s4,s3).
def coefficients(s):
    x,y,z,v,w = s
    return ((x,y,z,v,w),(z+w,v,y,x,w))

def offset(row, tail):
    return sum(x*y for x,y in zip(row[2:],tail))

def output(s,secret):
    return tuple(sum(x*y for x,y in zip(row,secret)) % q
                 for row in coefficients(s))

def add_errors(v, e):
    return tuple((x+y)%q for x,y in zip(v,e))

words = list(product(range(2),repeat=2))
honest,real,ideal = Counter(),Counter(),Counter()
for s in product(range(q),repeat=5):
    for r in product(range(2),repeat=5):
        for e in words:
            honest[s,add_errors(output(s,r),e)] += 1
for B in product(range(q),repeat=4):
    for w in range(q):
        s = (B[0],B[1],(B[2]-w)%q,B[3],w)
        rows = coefficients(s)
        assert tuple(x%q for row in rows for x in row[:2]) == B
        for tail in product(range(2),repeat=3):
            shifts = tuple(offset(row,tail) for row in rows)
            for secret in words:
                challenge = tuple(sum(x*y for x,y in zip(row[:2],secret))
                                  for row in rows)
                for e in words:
                    real[s,add_errors(add_errors(challenge,e),shifts)] += 1
            for u in product(range(q),repeat=2):
                ideal[s,add_errors(u,shifts)] += 1
assert honest == real and len(ideal)==q**7 and set(ideal.values())=={8}
print(sum(real.values()),len(ideal))
~~~

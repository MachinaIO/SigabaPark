---
title: A correctness alternative to rank-one witness enumeration
refs: [note:pq-we-short-rank-pencil, note:pq-we-rank-projection-noise]
tags: [witness-encryption, correctness, rank, complexity]
---

Consider the preceding real mode Y_i=S M_i r+e_i over a prime field and the uniform comparison mode for Y conditional on S. Suppose an honest satisfying witness gives nonzero coefficients a and a factorization M(a)=U V^T of inner dimension b. Assume the witness also specifies finite sets T_j of size at most s<q such that the scalar error in row j of Ya belongs to T_j simultaneously except with probability delta. These sets may depend on the witness and S but must be fixed independently of Y in the uniform experiment. Deterministic bounds follow, for example, by taking the signed sumsets of the honest error supports. Getting small sets is a substantive requirement. A row whose projected error is nearly uniform cannot have small support with high probability.

**Witness decoder.** Set X=SU and y=Ya. In the real mode some common c=V^T r satisfies y_j-X_j c in T_j at every good row. For each row form the polynomial in b formal variables z given by the product of (y_j-X_j z-v) over v in T_j. Replace every nonconstant monomial of degree at most s by a distinct unknown shared across all rows. Keep the constant monomial equal to one. Decode zero when this affine linear system is consistent, one otherwise. This is a use of the polynomial linearization method of [Arora and Ge](https://users.cs.duke.edu/~rongge/LPSN.pdf). No uniqueness of a solution or consistency between its monomials is required. The correct monomial values supply a solution in the real experiment on the good event.

**Uniform-mode proof accounting for the relaxation.** Conditional on S and the fixed witness, y_j are independent uniform because a is nonzero. For each of the q^D possible assignments to the relaxed monomials, where D=binom(b+s,s)-1, each resulting row equation is monic as a polynomial in y_j of degree |T_j|. Indeed the leading power of y_j multiplies only the constant monomial. Hence for any fixed assignment the probability all equations hold is at most (s/q)^t for t rows. The union bound includes spurious solutions of the relaxation and gives at most min(1,q^D(s/q)^t). The real-mode error is at most delta. These guarantees concern each fixed valid witness. At constant s and polynomial b, building the coefficient arrays by repeated linear-factor multiplication and testing consistency by field elimination take polynomial bit time for polynomial t and log q. Ciphertext length is t(d+k) field elements in the uncompressed pencil model. The row count is a cost of this approach and the fixed YES decoder can use the public worst-case bounds even when the actual projected supports are smaller.

**Arithmetic control.** For b=16, s=3, q=65537, D=968, the sufficient inequality 2^128 q^D s^t <= q^t first holds at t=1084. There are 1,050,396 entries in the dense augmented system. This prices a decoder that allows arbitrary c in the field, even when listing its possible values is prohibitive. It does not price a complete WE construction. The actual honest projected errors must satisfy the promised support bound; an error distribution with tiny support before projection need not do so afterwards. A separate NO proof must justify the *same* number of rows and the actual secret/error laws from a fixed falsifiable game. Increasing the number of rows can change the hardness premise. A public pencil generator of comparably low rank and comparably small projected support would also make this test available without a satisfying witness. Thus the required advantage comes specifically from the witness-dependent projection. The result supplies a YES correctness target, not a reduction from CircuitSAT or a NO security theorem.

The following exact integer checks reproduce the row threshold and independently enumerate all uniform right-hand sides in a small case. The example uses b=1, T={0,1}, and enumerates both unconstrained relaxed monomials. Its exact accepted set includes every honest right-hand side.
~~~python
from itertools import product
from math import comb
b,s,q,t = 16,3,65537,1084
D = comb(b+s,s)-1
assert (1<<128)*q**D*s**t <= q**t
assert (1<<128)*q**D*s**(t-1) > q**(t-1)
print(D,t*(D+1))
q=5
xs=(1,2,3,4,1,2)
accepted=set()
for z1,z2 in product(range(q),repeat=2):
    roots=[[y for y in range(q)
            if (y*(y-1)+(1-2*y)*x*z1+x*x*z2)%q==0] for x in xs]
    accepted.update(product(*roots))
for c in range(q):
    for noise in product((0,1),repeat=len(xs)):
        assert tuple((x*c+v)%q for x,v in zip(xs,noise)) in accepted
assert len(accepted)<=q**2*2**len(xs)
print(len(accepted),q**len(xs))
~~~

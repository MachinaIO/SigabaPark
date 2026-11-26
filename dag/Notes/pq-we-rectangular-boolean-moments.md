---
title: Compressing Boolean moment matrices by a shared space of affine forms
refs: [note:pq-we-bilinear-syndrome, note:pq-we-affine-certificate, definition:WE_CircuitSAT]
tags: [witness-encryption, construction, preprocessing, correctness]
---

Use affine elimination on Boolean wire constraints first. Carry inconsistent affine equations to an immediate false branch. On the remainder, free variables are v in GF(2)^n, and each remaining NAND contributes an affine expression plus a product of two known affine forms a(v), b(v). The baseline may use all wires as variables. Products with zero or equal linear parts are affine by Boolean idempotence and can also be eliminated. In particular z*(1+z)=0 as a polynomial function, so the tautological padding in the preceding connected-family example folds when its affine predecessor has been substituted. This simplification alone is not a general-purpose security argument.

**Find a common small row space.** In the dual space of the free variables, each remaining product defines a two-dimensional plane spanned by the linear parts of a,b. Choose a t-dimensional subspace U meeting each plane nontrivially. Fixing the t basis evaluations of U makes every product affine: besides fixing either operand it suffices to fix their XOR, since ab=a(a+b)+a. Conversely the quadratic part of ab restricted to the kernel of U is zero precisely when the restrictions of the two linear parts are dependent (polarize the product). Thus this is an exact criterion for simultaneous affinity of these individual products on each slice. Search with a preset cap t by branching on the three nonzero vectors of an unhit plane. Every solution extending the current space contains one of them, and every branch adds one dimension. This gives O(3^t poly(n,g)) time and polynomial space via depth first search; a branch that would exceed the cap can stop before extending. The DAG's affine certificate already supplies the three operand orientations; here the criterion gives an exact capped search and a rectangular ciphertext. For independent coordinates u,a_1,...,a_g the family of products a_i(a_i+u) needs rank g if one must select literal operands (project modulo u), whereas selecting the common direction u needs rank one. This family uses affine operands after substitution.

**Rectangular system.** Use a (t+1)-by-(n+1) matrix Y. Enforce Y00=1 and Y_i0 equal to the i-th basis form of U applied to the first-row bits. Use the chosen orientation to express each gate product as an affine remainder plus the product of an affine function of the left basis values with an affine function of v. Replace that product by its bilinear coefficient pairing with Y, using the two homogeneous indices; impose all resulting linear equations as H vec(Y)=s. Every real trace gives Y=(1,Uv)(1,v)^T. Conversely any rank-one feasible Y equals the outer product of its first column and first row by Y00=1; these must satisfy all the original gate and pin constraints. NO ranks are consequently among 2,...,t+1 even when n and the number of gates grow independently of t. The symmetric odd-rank lemma is unnecessary. Using the preceding signed filter at these t ranks yields perfect hiding, a raw length (t+1)(n+1)+1 and rank-one witness correlation at least exp(-3)2^-t: use log(1-x)>=-2x for x<=1/2 and sum_{r>=2} 2^-r=1/2.

**A cheaper erasure construction on the same system.** Independently choose uniform z in GF(2)^t and transmit z publicly. Use the usual row mask (H^T a,s^T a+b) and add to its matrix part a matrix N uniform subject to (1,z)^T N=0 (view (1,z) as a column on the left). Sample its bottom t rows uniformly and compute its top row from them. The polarity of every candidate character Y conditioned on z vanishes unless (i) H vec(Y)=s and (ii) every column of Y is proportional to (1,z). Every such feasible Y has rank one. On NO all message-dependent Fourier coefficients are zero for each public z. On YES the witness knows Uv and can test z=Uv before decoding; on a match its noise parity is identically zero. Thus ceil(lambda*2^t) independent samples give erasure probability at most exp(-lambda), using only additions, bit products and equality tests. Enumerating all 2^t labels with independent masks gives perfect correctness and perfect secrecy with no lambda repetition. This exploits a publicly recognizable match and so does not obey the private-count sampler restriction in the signed-polynomial bound.

**Accounting and baseline.** All-label ciphertext length is 2^t*((t+1)(n+1)+1) bits in lexicographic order with implicit labels. With fixed H and independent masks, Enc costs 2^t times a polynomial in n,t,g after preprocessing, and the receiver computes its label and reads that slot (or scans the full message on a sequential machine). This is polynomial for a known logarithmic cap and does not depend exponentially on extra wires. However the sender can also enumerate those same labels, solve one affine system per label, and decide SAT before emitting a single bit. Thus the rectangular construction is a witness-decoding interface and a structural accounting result, not a competitiveness claim against that baseline. A cap failure on a general circuit supplies neither a secure fallback nor a fixed-game reduction.

The check below compares the capped three-way search against enumeration of all subspaces through dimension two in a four-dimensional dual space; it also counts the signed parity over all noise matrices of the smallest two-by-three erasure channel.
~~~python
from itertools import combinations, product
from random import Random
rng=Random(7)
zero=frozenset([0])
def extend(U,a): return U|{x^a for x in U}
def search(lines,U,k):
    missed=next((line for line in lines if not line & U),None)
    if missed is None: return True
    return k>0 and any(search(lines,extend(U,a),k-1) for a in missed)
planes=list({frozenset((a,b,a^b)) for a,b in combinations(range(1,16),2)})
spaces=[{zero}]
for _ in range(2):
    spaces.append({extend(U,a) for U in spaces[-1] for a in range(16)})
for _ in range(256):
    lines=rng.sample(planes,rng.randrange(1,9))
    for k in range(3):
        assert search(lines,zero,k)==any(all(U & l for l in lines) for U in spaces[k])
for z,top,bottom in product(range(2),range(8),range(8)):
    parity=sum((-1)**(((z*top ^ bottom)&row).bit_count()%2) for row in range(8))
    assert parity==8*(bottom==z*top)
print("768 subspace comparisons; 128 channel characters")
~~~

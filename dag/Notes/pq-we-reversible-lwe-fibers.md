---
title: Reversible local LWE switches and compression of affine conjugates
refs: [note:pq-we-anchored-lwe-products, note:pq-we-successive-lwe-masks]
tags: [witness-encryption, reduction, complexity]
---

**Returning to the biased distribution.** Let X be a fixed-statement joint ciphertext law including public auxiliary data. In the additive output space choose a direction space V. Write U_V X for X plus an independent uniform element of V, leaving the auxiliaries alone. The anchored group simulation gives X approximately U_V X for an eligible group (in its current experiment) with advantage epsilon at the specified quantum runtime. Given auxiliaries and a canonical representative of the coset mod V, apply any efficient permutation of the fiber coordinates, possibly depending on that representative. Denote the resulting reversible transformation by F. Conditional on these controls U_V X is exactly uniform in its fiber, so F(U_V X) has the identical joint law. Passing from X through this common distribution to F(X) costs at most 2 epsilon, with the runtime of F charged in the second test. No independence of X's original fiber values from the controls is needed. This yields a switch between two biased laws; no permanent fresh pad need remain at the end. If the controls read inside the fiber the entire induced map there must still be a permutation.

**When moving the direction actually helps.** Suppose X is also exactly invariant under public affine bijections g_j(x)=A_j x+b_j, acting trivially on auxiliary data. Take a common action on output indices for every matrix entry. Then X approximately U_(A_j V) X with the *same* loss as the base switch by conjugation. The same holds for arbitrary words in these symmetries; only the efficiently applied word's cost enters. This can hide directions which no physical group exposes directly. For example take two independent identical copies of a complete block law with a perfectly exchangeable public framing. The swap transfers an independently established one-block shift to its counterpart without a new assumption. Exact invariance of the full view is essential, including every exposed output.

For explicit generator matrices compute the linear span W of all conjugate directions by starting with a basis of V and adjoining independent A_j images of existing basis vectors until no extension is possible. The terminal span is invariant under all A_j; finite dimension and invertibility imply invariance under the inverses as well. Each selected basis vector can be stored as a word applied to an original vector, of length at most the ambient dimension h. If the base switch gives a uniform pad on a multidimensional V at loss epsilon, it gives a pad on any line in V at loss at most 2 epsilon by the common uniform-V comparison. For a single base line its original bound suffices. Conjugate these switches and add their independent pads successively, using postprocessing on both sides to include pads already added. The total loss to uniformize W is at most 2 dim(W) epsilon. The statement also holds for matrix-valued line pads using the same action on indices. If the original invocation is built from b fixed LWE column challenges, include the b factor in epsilon. There is no exponential orbit enumeration.

**Limit.** Even nonlinear reversible gates that preserve each original fiber change a sample only by a vector in that direction space. Interleaving such gates with the affine symmetries changes the output modulo W only by the corresponding composition of the affine symmetries. In particular all these gates provide no extra pad direction on the quotient via this argument. Conjugating every gate by one common efficient nonlinear change of coordinates merely transports the same statement back through that bijection. Thus reusing a direction and disguising it by a change of coordinates is insufficient to produce an exponentially long indispensable witness-indexed masking proof of this form. This is a bound on the stated proof mechanism. It is not a lower bound on all WE reductions. A general construction would still need a local switch whose effect on the *remaining* conditional experiment is not described by this common affine quotient, together with an efficient simulation from a statement-independent game.

**Exact finite checks.** The first test permutes a partially uniformized law via two different nonlinear fiber permutations selected by correlated control values and checks every joint probability. The second compares basis closure with full group-orbit enumeration for two invertible binary transformations at dimension six.
~~~python
from collections import Counter,deque
from itertools import product

def gate(control,x):
    if control:
        return x ^ (4 if x&3==3 else 0)
    return x ^ (1 if x&6==6 else 0)

before,after=Counter(),Counter()
for control,x in [(0,2),(1,3),(1,5),(1,5)]:
    for pad in range(8):
        before[control,x^pad]+=1
        after[control,gate(control,x^pad)]+=1
assert before==after
def rotate(x):
    return ((x<<1)&63)|(x>>5)
def shear(x):
    return x^(2 if x&1 else 0)
gens=(rotate,shear)
queue=deque([1])
orbit={1}
while queue:
    x=queue.popleft()
    for g in gens:
        y=g(x)
        if y not in orbit:
            orbit.add(y)
            queue.append(y)
def span(vectors):
    H={0}
    for v in vectors:
        H |= {x^v for x in H}
    return H
basis=[1]
for x in basis:
    for g in gens:
        if g(x) not in span(basis):
            basis.append(g(x))
assert span(basis)==span(orbit)
print(len(before),"joint atoms;",len(orbit),"orbit vectors;",len(basis),"basis vectors")
~~~

---
title: Consistency checksums and message masks on matrix paths
refs: [note:pq-we-symbolic-slices, note:pq-we-tree-encodings]
tags: [witness-encryption, branching-programs, construction, correctness]
---

Consider a public layered graph for verifying a gate trace. Each path checks local predicates, selecting a legal truth-table row per gate; an accepting path has the desired output. Label disagreements across occurrences of the same wire by a binary syndrome e(path): use a spanning star of equality tests per wire, with each local choice contributing its endpoint bits by XOR. Constants and the output can be checked locally. Then e=0 on an accepting path is equivalent to a consistent satisfying trace. The graph has polynomial size even if local choices are made independently across gates. A witness selects a path in polynomial time.

For a public random binary k-row projection into the additive group of F=GF(2^k), define h(path) as the sum of the projected edge contributions. For any fixed inconsistent path the probability h=0 is 2^-k. With A an upper bound on the number of accepting paths, the probability of *any* such collision on a false circuit is at most A/2^k. For g four-row gates A<=4^g, so k=2g+lambda suffices, polynomial even though |F| is exponential. A fixed irreducible polynomial or a verified field representation is needed for field operations. Compression to one field element per running checksum does not itself enforce access to the message. The question here is whether a masked matrix product can release it only at h=0.

**Polynomial path masks.** Choose independent uniform field coefficients c_1,...,c_D and embed the message bit as the constant b in P(X)=b+sum_{i=1}^D c_i X^i. For any path the intended output is P(h). A consistent accepting witness obtains b exactly. This output can be evaluated by a width D+1 linear matrix program: an edge with increment a maps the row (1,x,...,x^D) to (1,x+a,...,(x+a)^D) via the binomial formula in the field, with start x=0. Compose with the local verifier by carrying its public state and allowing readout only at accepting states. This is polynomial for polynomial D and k. Revealing the terminal coefficient vector directly exposes b. Even an ideal interface revealing *only* the prescribed accepting-path outputs has a more general limitation.

Conditional on the public checksum projection, let S be the set of distinct reachable accepting checksums. If 0 is absent and |S|<=D, the outputs on *all* accepting paths jointly have a law independent of b: the evaluations of X through X^D have full row rank on S by a nonsingular Vandermonde minor and the nonzero evaluation points. Alternatively the shift polynomial 1+product_{s in S}(1-X/s) is zero at 0 and one on S. This is an information-theoretic property of the ideal outputs, not a circuit-hiding claim about the matrix representation. If D+1 distinct checksum paths are efficiently accessible, their outputs interpolate P(0) exactly. Secret change of basis on internal matrix states cannot alter those outputs. Merely increasing the bit length k decreases the probability of a collision at zero but cannot prevent interpolation.

**Connected false controls with many accessible checksums.** Take the connected core t=NAND(x,x), f=NAND(x,t), o=NAND(f,f). It is identically zero. Designate the final output one in the local accepting-path test. Pin all chosen core gate rows to the ordinary evaluation on x=0 except at the final gate, where choose a legal row with output one (for example inputs 0,0). This violates wire consistency on the core. Here pinning describes our selected paths, not extra circuit constraints. Add independent inputs z_i, one NAND(z_i,z_i) per input, and conjoin those outputs with o by two-NAND AND gates. Every gate is in the output cone and the resulting circuit stays identically zero. Choose each extra NAND row to have input pair (0,0) or (0,1); both give output one. All AND rows may now be legally chosen for inputs both one. In a spanning star comparing the two input occurrences of each z_i, the discrepancy bit is exactly the chosen switch. The 2^m resulting paths have pairwise distinct syndromes with a fixed nonzero core component. For any D+1<=2^m take the first D+1 switches in binary order; they are efficiently constructible if D is polynomial. With probability at least 1-(D+1)D/2^(k+1) their checksums are pairwise distinct. Interpolation then recovers b from one encryption. This calculation applies even if every tested checksum is nonzero. An encoding of the transition matrices would therefore have to change the family of released path values, not merely protect intermediate states. Different circuit preprocessing can change this control.

The exact calculation below uses GF(16) with modulus X^4+X+1 and every mask polynomial of degree at most two with prescribed constant. It compares the complete two-path laws and interpolates both possible messages from three nonzero paths for every choice of coefficients.
~~~python
from collections import Counter
from itertools import product
def mul(a,b):
    y=0
    while b:
        if b&1: y ^= a
        b >>= 1
        a <<= 1
        if a&16: a ^= 19
    return y
def inv(a):
    return next(i for i in range(1,16) if mul(i,a)==1)
S=(2,5,7)
weights=[]
for s in S:
    v=1
    for t in S:
        if t!=s: v=mul(v,mul(t,inv(t^s)))
    weights.append(v)
joint=[Counter(),Counter()]
for b,c,d in product(range(2),range(16),range(16)):
    vals=[b^mul(x,c^mul(x,d)) for x in S]
    joint[b][tuple(vals[:2])]+=1
    assert b==mul(weights[0],vals[0])^mul(weights[1],vals[1])^mul(weights[2],vals[2])
assert joint[0]==joint[1] and len(joint[0])==256
print("512 interpolations; two identical 256-point laws")
~~~

---
title: Exact distance of the gate-table syndrome encoding for CircuitSAT
refs: [note:pq-we-noisy-parity, note:pq-we-projected-syndrome, definition:WE_CircuitSAT]
tags: [witness-encryption, coding, construction, correctness]
---

For a Boolean circuit of g>=1 NAND gates with a designated output gate, remove gates outside the output cone. Use an odd-parity block of four selector bits at each gate, indexed by its four legal input/output triples. Define each pin value as the XOR of the corresponding pin bits of all selected triples. Impose equality of the pin values at occurrences of the same wire (a star of equalities suffices), fix constant wires, and require output one. All equations, including the block parities, form a binary syndrome system Hv=s on 4g columns and O(g) rows. Fixed constants refer to inputs; the designated gate output is a separate wire. A satisfying assignment selects exactly one triple per gate and is a weight-g witness. Encoding, witness lifting, and the original noisy parity Enc and Dec are polynomial. This realizes an exact short-syndrome decision reduction, but its distances determine whether the ciphertext can hide a bit.

**Exact minimum.** The four NAND triples are affinely independent over GF(2): relative to (0,0,1) the other three differences are (0,1,0),(1,0,0),(1,1,1). Thus each arbitrary pin tuple has exactly one odd selector: a singleton for a legal tuple and a triple for an illegal one. Every wire labeling with the required constants and output induces exactly these gate selectors; conversely any feasible selectors induce such a labeling on all used wires. The exact distance is

    min wt(v) = g + 2 min_labeling #{violated gates}.

For a false circuit, evaluate it on any input and flip just the designated final wire after evaluation. The final gate is the only violated gate. Hence the minimum is exactly g+2, and a representative is publicly computable without solving any search problem. For a true circuit the minimum is g. The bit recovery correlation using any such v on the noisy channel is rho^wt(v), unchanged by the projected-syndrome variant. If rho^g >= 1/2 for the desired YES correctness, the false-circuit correlation is at least 2^(-(g+2)/g) >= 1/8, already exceeding the 1/64 weak target. Even improving the fraction of violated gates with checks made only of NAND tables cannot by itself give the needed distance ratio: every wire labeling respecting the pins has a representative of weight at most 3g. This last statement assumes compatible wire and pin equalities. It concerns this local table encoding and parity channel.

**Arity alone does not remove the repair.** For any nonaffine scalar Boolean function f and every input x, the wrong-output tuple (x,1+f(x)) is the XOR of three legal tuples. Otherwise all second differences f(x)+f(x+a)+f(x+b)+f(x+a+b) would vanish for every a,b, since the three legal inputs x+a,x+b,x+a+b sum to x. Then a -> f(x+a)+f(x) would be additive and f affine, a contradiction. The three inputs are distinct for a nonzero second difference. For an affine f the legal graph is affine and the wrong output is outside its affine hull. Thus increasing the fan-in of a nonaffine single-output gate still caps its local repair cost at three in an odd-selector table. This narrows the construction question to enforcing consistency beyond these pin parities, or changing the observation that a short approximate execution can decode. The fixed LPN hybrid computes the same parity and cannot supply the missing NO guarantee.

The listing enumerates all functions of up to three inputs and checks the legal-triple repair at every wrong-output tuple for exactly the nonaffine functions. Separately it enumerates the full syndrome fiber of a three-gate identically false circuit, using only the odd-block, wire and output equations.
~~~python
from itertools import product, combinations

cases=0
for arity in (1,2,3):
    width=1<<arity
    for bits in range(1<<width):
        f=[(bits>>x)&1 for x in range(width)]
        affine=all((f[x]^f[0])==sum(((x>>i)&1)*(f[1<<i]^f[0])
                    for i in range(arity))%2 for x in range(width))
        graph=[2*x+f[x] for x in range(width)]
        triples={a^b^c for a,b,c in combinations(graph,3)}
        assert all(((p^1) in triples)==(not affine) for p in graph)
        cases+=width
table=[(x,y,1^(x&y)) for x,y in product(range(2),repeat=2)]
def pins(mask):
    return tuple(sum(t[i] for j,t in enumerate(table) if mask>>j&1)%2
                 for i in range(3))
# t=NAND(x, NAND(x,x)) is always 1;
# NAND(t,t) is always 0.
blocks=[(pins(m),m.bit_count()) for m in range(16) if m.bit_count()%2]
weights=[i+j+k for ((a,b,c),i),((d,e,f),j),((h,l,o),k)
         in product(blocks,repeat=3) if a==b==d and e==c and h==l==f and o]
assert min(weights)==5
print(cases,min(weights))
~~~

**A repair for circuits admitting bounded-degree refutations.** Add global variables y_S for multilinear wire monomials of degree <=D, including y_empty fixed to one. Tie the degree-one variables to pin parities. For each gate polynomial 1+ab+c=0 and pin polynomial, add every equation obtained by multiplying it by a squarefree monomial of degree <=D and reducing by x_i^2=x_i, retaining products whose formal multilinear expansion has degree <=D. Linearize by replacing each monomial by y_S. In the noisy parity encryption use noise on the selector columns alone; set all auxiliary column noise to zero. Every satisfying trace lifts by evaluating all monomials, so its parity still sees exactly g independent noisy positions. For any NO instance on which a linear combination of these lifted rows proves 1=0, the augmented target s lies outside im H. There exists a mask shift a0 with H^T a0=0 and s^T a0=1. Pairing a with a+a0 gives *identical* message distributions. For fixed D the augmented system has polynomial size (O(g^(D+1)) candidate rows for O(g) wires), with polynomial Enc and Dec. Existence of this kind of refutation is decidable by elimination; unrestricted-degree coverage at polynomial size is not established. This is a sufficient condition for the repair, not a hardness assumption.

On the exhaustively checked three-gate example the global repair works already at D=2. The equations on wires x,c,f,o reduce to 1+x+c=0, 1+xc+f=0, 1+f+o=0, and o+1=0. Multiplying the first by x and multilinearizing gives xc=0. The sum of this equation and the last three is the contradiction 1=0. Thus the same false circuit that has a public weight-five repair for three honest selector positions acquires perfect hiding with the added degree-two columns and rows.

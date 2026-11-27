---
title: Partitioning a point-insertion hop by the first erroneous gate
refs: [note:pq-we-path-checksum-masks, definition:WE_CircuitSAT]
tags: [witness-encryption, construction, reduction, correctness]
---

The APG' walk in [PR 111, sections 4 and 7](https://github.com/MachinaIO/SigabaPark/blob/ad17be24e746d72cc18d17819818f9a2c8efbc60/dag/Notes/pq-we-exposed-root-reachable-lemma.md) inserts a point in the original input bits. In the level order of the [base construction, section 6](https://github.com/MachinaIO/SigabaPark/blob/ad17be24e746d72cc18d17819818f9a2c8efbc60/dag/Notes/pq-we-native-hop-designs.md), input bits are followed by Tseitin gate values. A pad for input k therefore changes an entire *fiber* of level strings (k,y). A clause violated at the correctly evaluated y need not be violated at another y. For a circuit with a separate output unit and unfixed gate variables, each individual gate clause can be satisfied on some extension of k (choose predecessors, then compute that gate), and the output unit can separately be satisfied by setting the output to one. This matters for a proposed embedding into one fixed clause block; it does not refute the joint PI claim.

**At most g+1 fixed-clause insertions per fiber.** Assume gate bits are read in topological order and the output pin is an explicit unit. Evaluate the g-bit honest trace t on k. When k is a nonwitness, t_out=0. Partition its extensions into the singleton y=t and, for i=1,...,g, the cylinders y_<i=t_<i, y_i=1-t_i. These are disjoint and exhaustive. The singleton violates the output unit. In the i-th cylinder both gate inputs have their honest bits and the output has its wrong bit. For NAND with inputs a,b and output c choose (not a or not b or not c) when a=b=1, (a or c) when a=0, and (b or c) otherwise. The selected clause is violated throughout that cylinder, independently of every remaining bit. This rule also works for repeated inputs. Finding all g+1 labels takes one circuit evaluation and O(g) further gate operations. Represent a prefix by its length and a pointer to t with a last-bit flip, avoiding quadratic storage.

**A merge order with small live width.** Insert the singleton first. Starting at i=g and working down to one, insert its i-th sibling cylinder and merge the two live children into their common parent. Before each sibling insertion the accumulator is the cube with y_<=i=t_<=i (and the fixed k); after the merge it has prefix y_<i=t_<i. After g merges it is exactly the original k-fiber. Earlier input fibers can remain represented by the existing external slots. At most two new *live* cylinders are needed at any one time in this refinement, irrespective of g. This count does not establish that dead APG' slots already have the required prefix programs or that reshaping their encoded rows is free.

Consequently a sufficient refinement target is insertion of a prefix cylinder labeled by a single persistently violated Tseitin clause, with arbitrary suffix after its prefix, in the presence of the accumulated sibling and the external pads. It must simulate the full public encoding jointly. If such insertions, the required slot preparation, and the merges all have justified indistinguishability bounds, ordinary hybrid addition costs at most (g+1) insertion losses plus g merge losses and preparation losses per input, with the original external merges counted separately. For g=4096 this substitutes 4097 insertions and 4096 internal merges for one fiber insertion; there is no 2^4096 enumeration. The published co-located flip does not automatically apply to the insertion: the selected clause can remain active on other prefixes and need not have a shared pad secret. No PI proof, shorter ciphertext, or improved LWE estimate follows solely from this combinatorial refinement. Reordering an already encoded non-topological trace would require a separate compiler argument.

The check exhausts every tail of each sampled false-input fiber, verifies its designated clause, and replays the sibling merges by their exact sets. It includes fanout and tied operands.
~~~python
from itertools import product
from random import Random
rng=Random(37)
fibers=extensions=0
for g in range(1,8):
    for _ in range(16):
        gates=[(rng.randrange(i+2),rng.randrange(i+2)) for i in range(g)]
        for k in product(range(2),repeat=2):
            vals=list(k)
            for a,b in gates: vals.append(1^(vals[a]&vals[b]))
            t=tuple(vals[2:])
            if t[-1]: continue
            groups=[set() for _ in gates]
            for y in product(range(2),repeat=g):
                extensions+=1
                if y==t:
                    assert y[-1]==0
                    continue
                i=next(j for j in range(g) if y[j]!=t[j])
                a,b=gates[i]
                trace=k+y
                if vals[a]==0: assert (trace[a]|y[i])==0
                elif vals[b]==0: assert (trace[b]|y[i])==0
                else: assert trace[a]&trace[b]&y[i]==1
                groups[i].add(y)
            acc={t}
            for i in reversed(range(g)):
                assert not acc & groups[i]
                acc |= groups[i]
                assert acc=={t[:i]+s for s in product(range(2),repeat=g-i)}
            fibers+=1
print(fibers,extensions)
~~~

### A two-state program for the other prefixes of the same violated clause

Consider a target cylinder whose first L-1 bits equal P and whose L-th bit is b*. The fixed violated clause is represented by a single scalar clause block: its scalar gate q_i(b) is one exactly when the bit does not satisfy any clause literal at level i. (Equivalently this is the indicator that falsifying the clause is still possible.) All positions after L are unrestricted, every test along P passes, and q_L(b*)=1. These are properties of the fixed-clause cylinders above when the insertion level is taken to be their last fixed bit. Handle an empty cylinder prefix separately. For clarity this calculation uses equal unit start weights and a common bit-dependent secret for the displayed blocks. It is a proposed change to the slot interface, not a property of the existing independently keyed constraint and pad blocks.

Before level L, use four scalar coordinates (target d, clause Q, waiting u, diverged v). The last two form one deterministic two-state program. Start on u. Gate both states by q_i(b); while live, u moves to v at the first disagreement with P and v stays there. The target follows P and Q follows the clause gates. Then for every depth i<L every live prefix has one of just two activity rows:

    p=(1,1,1,0)  when it agrees with P;
    h=(0,1,0,1)  when it has departed from P and still passes the clause tests.

All other prefixes give the zero row. This follows by induction, including a prefix departing and subsequently failing a clause test. Every transition sends each displayed row to p,h or zero. With a common gamma-tensor secret the actual row for a word is its activity row tensored with that word's secret product. Hence retaining these two block-row combinations contains all of this gadget's prefix exposures, independently of the number of different departing prefixes. Complete p,h by the coordinate rows e_Q,e_u. The inverse recovers d=p-Q-u and v=h-Q, so integer lift entries have absolute value at most one at every depth. This is the reachable-row and short-lift algebra sought in section 2 of PR 111, restricted to the proposed gadget. It is not the separate preimage-distribution hypothesis of that lemma.

At level L discard waiting (zero outgoing row), keep diverged active when the clause gate passes, and flip only d on b*. The active Q and v coordinates continue with all-one suffix gates. In the retained target-branch rows the Q/v contributions are (U,U+V), with the toggled term X entering the first row only. If U,V were fresh independent uniforms jointly with the rest, (U+X,U+V) would be uniform conditionally on X and its auxiliary view: the two-by-two mixing matrix has determinant one over any modulus. The same triangular map works on vectors of child samples if joint fresh uniforms have been justified for all active children. With only Q as reservoir the two exposed rows instead read (U+X,U), and differencing retains X. Thus one extra *diverged state* fixes the local linear algebra for arbitrarily many departures. The statement is about the noised-target hybrid with the indicated uniformity premise; exact algebra does not make the original GGH15 targets uniform.

**Embedding debt.** The auxiliary accepting state contributes a new independent terminal pad throughout Q outside P at the target child. Some of those strings can be later than the insertion point and unpadded in the actual hybrid. An example has P starting with 0 and a clause depending only on the last fixed bit: every prefix starting with 1 and passing that literal is a departure. Simply adding the new state need not preserve the joint public law there. Tying its terminal row to Q to avoid a new independent value also destroys the rank-two uniformity used above. A complete insertion proof would have to implement the state inside an existing reservoir, or justify a separate replacement for those other strings, as well as use a common secret and prove the needed multi-row preimage hybrids. The calculation removes a width obstacle in the proposed repair and isolates where the missing randomness is required. It does not give PI or a revised ciphertext cost.

The check enumerates all target prefixes, choices of which earlier clause tests are active, and all prefix paths through depth five. It also enumerates the mixing laws for each possible toggle modulo 2, 3, and 4.
~~~python
from itertools import product
from collections import Counter
p=(1,1,1,0)
h=(0,1,0,1)
for depth in range(6):
    for target,tests,path in product(product(range(2),repeat=depth),repeat=3):
        d,Q,u,v=p
        for i,(a,test,b) in enumerate(zip(target,tests,path)):
            same=int(a==b)
            live=int(not test or same)
            d,Q,u,v=d*same,Q*live,u*same*live,(v+u*(1-same))*live
            expect=(p if path[:i+1]==target[:i+1] else h) if Q else (0,0,0,0)
            assert (d,Q,u,v)==expect
for modulus in (2,3,4):
    for X in range(modulus):
        law=Counter(((U+X)%modulus,(U+V)%modulus)
                    for U,V in product(range(modulus),repeat=2))
        assert len(law)==modulus**2 and max(law.values())==1
print("depths 0 through 5; moduli 2, 3, 4")
~~~

## Inserting across many inputs with a partial evaluation certificate

For the all-inputs-before-gates order, a public rejecting input prefix can certify many complete input fibers at once. Extend its assigned primary bits by three-valued NAND propagation in topological order. A known zero operand forces output one and supplies its binary Tseitin clause; two known ones force output zero and supply the ternary clause. Unknown values stay unconstrained. If the output is forced to zero, backtrack the justifications from that output, keeping one zero operand when there is a choice and both one operands otherwise. Retain the distinct gate conclusions in topological order, say q of them. This cone, determined from the circuit and the prefix alone, certifies rejection on every completion. Nonselected operands may remain completely undetermined.

On the subcube defined by the prefix, use q+1 disjoint cubes of full (input,gate) traces. For cube i<=q fix the first i-1 selected gate conclusions to their certified values, flip selected gate i and stop. All free input bits and all unselected gate bits remain wildcards. Its justification clause fails identically: all operands needed by that clause are already fixed. The last cube fixes all q conclusions and violates the output unit. Conversely the first incorrect selected conclusion, or its absence, locates each trace in exactly one cube. Merge the two siblings on the last selected gate, then work back up to the first. For prefix length b and n inputs this replaces a per-completion partition with only q+1 local insertion obligations and q sibling merges across 2^(n-b) input fibers. These are generally wildcard cubes in the *original* coordinate order. A single product indicator represents each with both transitions live at wildcard levels. That representation alone does not give the public APG insertion or a law-preserving merge across skipped levels. A lemma requiring a contiguous fixed prefix cannot be applied unchanged.

A deterministic cover can explore input prefixes left-to-right, emitting a leaf once propagation forces rejection; otherwise split on the next input bit. For a false circuit every full assignment terminates. With L emitted leaves this visits 2L-1 prefixes and takes O(L*(n+g)) straightforward preprocessing, with a certificate for each leaf; stop at a chosen budget for a partial cover. When joining the leaves one must also account for L-1 binary input-prefix merges. This improves the count for structured formulas, with exponential worst case and no implication that a general polynomial-hop proof exists. At full depth the backtracked cone can still omit gates whose values are unnecessary. The obstacle for [PR 111 section 7](https://github.com/MachinaIO/SigabaPark/pull/111) is now specifically a joint public-encoding hop across the wildcard coordinates; the cover does not establish indistinguishability or reduce ciphertext length by itself.

~~~python
from itertools import product

# Bits x0,x1 head the input; unrelated gates depend on the eight free inputs.
n = 10
gates = [(2,3),(4,5),(0,1),(6,7),(8,9),(12,12)]
output = n+len(gates)-1
known = {0:0}
reason = {}
for z,(a,b) in enumerate(gates,n):
    zero = next((v for v in (a,b) if known.get(v)==0), None)
    if zero is not None:
        known[z],reason[z] = 1,[zero]
    elif known.get(a)==known.get(b)==1:
        known[z],reason[z] = 0,[a,b]
assert known[output]==0
needed = {output}
for z in reversed(range(n,output+1)):
    if z in needed:
        needed.update(reason[z])
forced = [(z,known[z]) for z in sorted(needed) if z>=n]
assert forced==[(12,1),(15,0)]
counts = [0,0,0]
for suffix in product(range(2),repeat=n-1):
    for y in product(range(2),repeat=len(gates)):
        vals = (0,)+suffix+y
        j = next((i for i,(v,b) in enumerate(forced) if vals[v]!=b),2)
        counts[j] += 1
        # Binary clause (x0 OR g12), ternary (!g12 OR !g12 OR !g15), output unit.
        assert not (vals[0] or vals[12]) if j==0 else (
               not ((not vals[12]) or (not vals[15])) if j==1 else not vals[output])
assert counts == [16384,8192,8192]
print("512 input completions and 64 gate assignments; three certified cubes",counts)
~~~

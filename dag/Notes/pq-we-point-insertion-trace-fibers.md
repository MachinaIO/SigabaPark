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

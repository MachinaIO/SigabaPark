---
title: Local rekeying on a violated-clause cylinder at the evaluator interface
refs: [note:pq-we-point-insertion-trace-fibers, note:pq-we-checksum-prefix-keys]
tags: [witness-encryption, reduction, construction, correctness]
---

Consider a modified evaluator on classical trace strings z of length h. Its only observable operation is coherent XOR access to
V_b(z)=b XOR the sum modulo two of F_j(z) over clauses j violated by z.
Here F_j is one output bit of a GGM tree with its own independent root. A valid witness recovers b with one call and no error. The evaluator takes O(mh) generator expansions for m clauses. This is an oracle interface, not a standalone public ciphertext. Handing out its circuit with b and the roots as constants discloses the secret.

**Local change.** Fix a public prefix p of length l on which clause j is always violated. For its tree let S be the seed at p and let the frontier be the l sibling seeds on the root-to-p path. They evaluate everything outside the cylinder. Replace S by S XOR D for a fresh independent lambda-bit D; use the new seed only below p. This realizes a change in the value there by XORing the *difference* of the two subtree functions on the suffix, with no change at any other input, including later prefixes that violate the very same clause. In particular this does not insert an independent additive GGH15 matrix-chain pad.

Even jointly with D, the frontier, every other independent clause root, and coherent access to the aggregate evaluator in the selected world, the original and rekeyed experiments differ by at most 2l generator distinguishing advantages with simulation overhead. In either experiment replace the successive child pairs down the target path by independent uniform pairs, from top to bottom. Each hop embeds a single fixed G(seed) versus uniform challenge; its parent seed need not be exposed. The final frontier and S are mutually independent uniform. Conditional on the frontier and D, S and S XOR D are then identically distributed. The reduction builds a reversible evaluator from the frontier, the available subtree seed and the other roots. It therefore incurs no guessing loss per suffix or quantum measurement of the query. For l=0 this equality already holds exactly. The original root, internal path ancestors, and a second oracle using the *other* seed are not part of the exposed view. Releasing an ancestor seed that derives S would invalidate this simulation.

Applying these changes sequentially to the g+1 first-error cylinders only needs disjoint subtrees: for each affected tree the previously modified sibling subtrees can be evaluated with their independent replacement offsets using the sibling frontier. With private tree state and oracle-only access, this gives a sum of at most 2(g+1)h single-challenge advantages for one input fiber, even though it has 2^g suffixes. This sum does not purport to expose every cylinder's frontier simultaneously: a sibling seed given away at one step could be an ancestor of another rekeyed subtree.

**What fixed hardness buys for values.** On a false circuit replace the m independent keyed functions by random functions, one per hybrid. For the quantum-query hybrid, independent ideal auxiliary functions queried at most Q' times can be simulated by 2Q'-wise independent functions: each amplitude has degree at most Q' in the oracle indicators and measurement probabilities degree at most 2Q'. For example use random field polynomials on an injective encoding of the h-bit domain and a fixed output bit. Account for a compute/uncompute factor in Q'. Quantum-query security of the GGM family from a quantum-secure length-doubling PRG is the existing [Zhandry theorem](https://eprint.iacr.org/2012/182.pdf). With all functions random, the aggregate is itself a uniform random bit-function: at each z at least one independent fair bit enters, and entries at different z use disjoint random cells. XORing the constant b leaves its full law unchanged. Consequently the two *oracle* games cost at most 2m qPRF distinguishing advantages. This argument uses only the observable values. In fact the simpler oracle that returns b on satisfying inputs and a single PRF elsewhere already has this property. The local rekey result is relevant because it additionally handles outside-subtree seed exposure and identifies the correlations that must be preserved.

**Gap to the actual construction.** PR 111 provides public preimages, root readings and separate matrix blocks. None of the calculations above simulates their joint law given a punctured frontier and one chosen subtree seed. A reduction would need to produce those public data without the master root or a challenge-path ancestor, with correct off-cylinder correlations, while still implementing the witness's public decoding operation. Supplying an oracle or granting just its coherent evaluations does not implement that step. The result suggests changing how the mask is generated rather than adding the unaccounted independent diverged-state pad, but proves no actual APG insertion.

The finite check uses two domain bits and the two contradictory unit clauses on the first bit, plus one redundant clause on the second bit. It counts all 4096 ideal function triples and all 16 possible aggregate truth tables for each message. A separate check verifies the final uniform-seed rekey bijection for every offset at seed width four.
~~~python
from collections import Counter
from itertools import product
hist=[Counter(),Counter()]
for f,g,r in product(range(16),repeat=3):
    table=0
    for z in range(4):
        selected=g if z&1 else f
        table |= (((selected ^ (0 if z&2 else r))>>z)&1)<<z
    hist[0][table]+=1
    hist[1][table^15]+=1
assert hist[0]==hist[1] and set(hist[0].values())=={256}
for offset in range(16):
    assert sorted(s^offset for s in range(16))==list(range(16))
print(len(hist[0]),sum(hist[0].values()),16)
~~~

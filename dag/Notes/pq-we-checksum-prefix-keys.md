---
title: Two prefix-key sets for a path checksum meet in the middle
refs: [note:pq-we-path-checksum-masks, definition:WE_CircuitSAT]
tags: [witness-encryption, branching-programs, reduction, construction]
---

Cut the public local-trace graph at a fixed layer. Encode a boundary vertex identifier followed by a k-bit checksum as an address of fixed length d. Let A be all addresses reached from the start and B those reached backwards from an accepting state (the suffix checksum uses the same additive binary group). An intersection concatenates two paths at the same vertex with total checksum zero. A satisfying witness determines one such address. With k=2g+lambda in the four-row gate graph the preceding union bound makes a spurious intersection on a false circuit occur with probability at most 2^-lambda.

**Fixed-game realization.** Take a length-doubling generator G with lambda-bit seeds, assumed indistinguishable from 2 lambda uniform bits against polynomial-size quantum tests on classical samples. Build the binary GGM tree by expanding each node seed to the seeds of its two children. Represent A,B by public prefix-free covers of their addresses; each prefix denotes a full binary subtree. Publish the seeds for the A cover from root K0. For bit zero publish the B-cover seeds from K0 as well; for bit one use an independent root K1. Covers, graph and projection are determined independently of the roots. On the witness address derive a leaf on each side and decode zero exactly when the two leaf strings agree. The generator assumption concerns only its security parameter and is efficiently testable with a sampled challenge bit. This construction uses the established GGM prefix restriction; see [Boneh and Waters](https://eprint.iacr.org/2013/352).

On a good NO projection the union of covers is prefix-free. For a prefix-free list the joint distribution of its node seeds is computationally indistinguishable from independent uniform seeds. In the minimal trie of paths to these nodes replace the output of each strict ancestor's expansion by a fresh uniform pair, in top-down order. The input seed of the next replaced expansion is then uniform and is neither published nor needed elsewhere. The simulator plugs in a *single fixed PRG challenge*, samples all other branches, and expands descendants normally. This proof works for classical strings against quantum tests without quantum oracle access. For the common-root branch the number of hops is at most dQ where Q is the total cover size; for separate roots the sum is also at most dQ. Consequently the raw distinguishing gap is bounded by the bad-projection probability plus 2dQ times a one-challenge bound with the simulation overhead (use a deterministic Q bound). One can condition on public covers or hardwire them for nonuniform tests. For a fixed true witness, bit zero always decodes correctly, and on bit one two independent leaf values coincide with probability at most 2^-lambda + 2d times the corresponding PRG bound. This is a computational bound on a classical correctness event.

**Construction time and length.** For an explicit graph perform forward and reverse dynamic programming on tries: XOR by an edge checksum maps a prefix to another of the same length by XORing the corresponding leading bits. Merge predecessor lists by union, deleting descendants of included nodes and coalescing sibling subtrees until canonical. Perform this per vertex before adjoining its identifier at the cut. Work is polynomial in the graph size, d, and the maximum *intermediate* trie size across layers, including temporary unions. Using up to d bits to encode each prefix plus length framing, the node payload and index cost O(Q(lambda+d+log(d+1))) bits plus the public projection if it is not already provided. Witness decoding needs at most 2d generator calls after address computation and lookup. This avoids publishing values of one low-degree polynomial on many paths.

**Limit for general CircuitSAT.** Whenever the two prefix lists are explicit, their intersection can itself be found in polynomial time by testing whether a prefix from one side extends a prefix from the other. With uniform polynomial preprocessing, exact or efficiently built outer covers that always preserve YES witnesses and overlap with only negligible probability on NO instances would give a randomized SAT algorithm. One cannot invoke ordinary constrained-PRF security for arbitrary succinct predicates to bypass this: that definition need not hide *common versus independent master keys*. For instance append an independent random identifier to the master key and copy it to every restricted key without using it in evaluation. It preserves ordinary off-domain value pseudorandomness by independent simulation but reveals common origin even on disjoint nonempty restrictions. The direct tree hybrid above is needed.

There is also a size obstruction for *exact* prefix descriptions, even allowing a shared invertible binary coordinate change. A translate of a linear space V contains two sibling leaves only if the last coordinate vector belongs to V. Otherwise every prefix in an exact cover must be a leaf. If the two sides of a one-vertex cut are affine m-spaces with disjoint direction spaces (intersection {0}), at least one needs 2^m prefix entries in every common linear coordinate system. Such sets arise from binary-choice chains adding independent vectors from disjoint basis blocks before and after the cut; a separate offset bit makes them disjoint. This is a representation bound, not a hardness claim. Outer covers can be much cheaper when a known separator exists. General efficient disjoint-key generation for the actual implicit checksum sets remains open.

The finite check enumerates every ordered basis in dimension four and verifies both the lower bound and exact intersection test. For the privacy hybrid it checks the structural invariant that every pair of nodes in the union has disjoint subtrees when the represented sets are disjoint. It does not test a cryptographic PRG assumption.
~~~python
from itertools import permutations

def image(a,basis):
    out=0
    for i,b in enumerate(basis):
        if a>>i & 1: out ^= b
    return out

def cover(S,p=""):
    if not S: return []
    if len(S)==2**(4-len(p)): return [p]
    return sum((cover({s for s in S if s.startswith(p+b)},p+b)
                for b in "01"),[])

count=0
for basis in permutations(range(1,16),4):
    if len({image(x,basis) for x in range(16)})!=16: continue
    def prefixes(domain):
        return cover({format(image(x,basis),"04b") for x in domain})
    a=prefixes(range(4))
    b=prefixes([0,4,8,12])
    assert max(len(a),len(b))==4
    overlap=lambda p,q: p.startswith(q) or q.startswith(p)
    assert any(overlap(p,q) for p in a for q in b)
    c=prefixes([4,5,6,7])
    assert not any(overlap(p,q) for p in a for q in c)
    count+=1
print(count)
~~~

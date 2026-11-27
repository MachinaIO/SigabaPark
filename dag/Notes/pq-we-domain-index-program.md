---
title: Witness indexing shrinks both dimensions of the diagonal WE encoder for finite-domain constraints
refs: [note:pq-we-compiler-transport, note:pq-we-unit-output-clause-groups]
tags: [witness-encryption, compilation, complexity, correctness]
---

Consider an explicitly declared finite-domain CSP given by forbidden partial tuples. Variable i ranges over k_i >= 2 values. An accepted assignment matches none of the forbidden tuples. This includes graph coloring and arbitrary tables of forbidden local configurations. When the input is a one-hot CNF, apply the translation only to certified exactly-one blocks with all remaining clauses of the forbidden-tuple form (negative indicators for specified values). An unrecognized input can retain its original encoding. The construction uses the standard binary representation of a finite-domain value and the original diagonal CNF encoder of [VWW, Construction 6.2](https://eprint.iacr.org/2022/1140). The comparison below concerns the choice of public input representation for that encoder.

Encode each value by d_i=ceil(log2 k_i) witness bits. For every forbidden tuple, emit the single clause which excludes the concatenation of its specified bit patterns. A missing variable in that tuple contributes no literals. Rule out out-of-range words by decomposing [k_i,2^d_i) into aligned binary prefix intervals. Exclude each such prefix by one clause on its leading bits. One can enumerate these intervals by starting at k_i and repeatedly adding its least significant set bit until reaching the power of two. This takes at most d_i steps and represents every invalid word exactly once. With an empty forbidden tuple the translated clause is empty. An original valid witness maps deterministically to its indices; every satisfying bit string decodes to a legal source witness. The equivalence holds pointwise, before the encryption algorithm runs.

For V variables and T forbidden tuples, explicitly pairwise exactly-one encoding has H=sum k_i levels and w=1+T+sum(1+binom(k_i,2)) coordinates including the message. Index encoding has H'=sum d_i and w'=1+T+sum popcount(2^d_i-k_i). Clause lengths can grow, but remain bounded by the total bit length of the participating indices. Both diagonal encoders have exactly two matrices per level, with binary entries for any clause lengths. Thus the same original false-instance security theorem can be invoked on each compiled public formula at parameters supporting its dimensions. There is no replacement of the tensor law or new evasive-LWE sampler hypothesis in this translation. In a concrete time-security claim budget the statement-specific machine or framing wrapper. Parameter selection must dominate both instances for the costs below to be compared at a common n and K.

For a 64-vertex cycle with 4 colors, T=256, the one-hot and index formats have (H,w)=(256,705) and (128,257). With common n,K and common gadget-width rule m=c n K w, the nonroot raw matrix bits and dense full-root path multiply-adds scale as (H-1)w² and the nonroot preimage columns as (H-1)w. The root payload scales as w and is accounted separately. These are exact ratios of these terms for the two formats, excluding public compilation, key generation, per-column sampling work and decryption preprocessing. For fixed k>=3, general k-colorability is retained, even though the cycle itself is easy. A sparse graph with bounded average degree and growing k has T=O(Vk), so the index encoding improves width from order Vk² to O(Vk) and height from Vk to O(V log k). This is a comparison with the explicit pairwise baseline only. Native binary input is already in the smaller representation. In particular this is neither a general worst-case improvement for CircuitSAT nor a new hardness assumption.

The following executable checks the emitted clauses, witness validity and exact backend resource ratios.
~~~python
from fractions import Fraction
from itertools import product

def exclude(start, length, value):
    # (position, Boolean polarity). This disjunction fails on precisely value.
    return [(start+j, 1-((value >> (length-1-j)) & 1)) for j in range(length)]

def compile_domains(sizes, forbidden):
    offsets = []
    clauses = []
    height = 0
    for size in sizes:
        width = (size-1).bit_length()
        offsets.append((height,width))
        first = size
        while first < 1 << width:
            block = first & -first
            drop = block.bit_length()-1
            clauses.append(exclude(height,width-drop,first >> drop))
            first += block
        height += width
    for item in forbidden:
        clause = []
        for i,value in item:
            start,width = offsets[i]
            clause.extend(exclude(start,width,value))
        clauses.append(clause)
    return height,clauses

checks = 0
for size in range(2,33):
    for forbidden in ([], [()], [((0,size-1),(1,1))]):
        h,clauses = compile_domains([size,3], forbidden)
        assert len(clauses) == ((1 << (size-1).bit_length())-size).bit_count()+1+len(forbidden)
        for word in product(range(2),repeat=h):
            split = h-2
            values = (sum(b << (split-1-j) for j,b in enumerate(word[:split])),
                      2*word[-2]+word[-1])
            source = values[0]<size and values[1]<3 and all(
                any(values[i]!=v for i,v in item) for item in forbidden)
            target = all(any(word[i]==bit for i,bit in clause) for clause in clauses)
            assert source == target
            checks += 1
edges = [((i,c),((i+1)%64,c)) for i in range(64) for c in range(4)]
h,clauses = compile_domains([4]*64,edges)
w = 1+len(clauses)
assert (h,w)==(128,257)
print(checks, float(Fraction((h-1)*w*w,255*705**2)),
      float(Fraction((h-1)*w,255*705)))
~~~

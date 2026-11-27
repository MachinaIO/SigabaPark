---
title: A 4096-NAND syndrome check with GF(2) rank at least 131072 across every balanced three-way cut
refs: [definition:WE_CircuitSAT_Capped, theorem:AdvancedEncryption.WE.PublicSlices.syndrome_minor, theorem:AdvancedEncryption.WE.SplitRank.disjointness_rank]
tags: [witness-encryption, communication-rank, circuit-sat, code]
---

The earlier disjointness example certifies exponential rank for a *fixed* paired-bit split. The following public linear-code check simultaneously gives a concrete lower bound at every permutation of a 42/43/43 partition, whether the endpoint is the first, middle or last chunk. It is easily satisfiable; the obstruction concerns exact public separated features for the predicate, not WE security or the complexity of deciding SAT.

### A finite, reproducible binary check matrix

Let column j for 0≤j<128 encode 20 binary check coordinates. In the byte-polynomial representation with reduction by X⁷+X+1, pack the constant one, the seven bits of j, the seven bits of j³, and the low five bits of j⁵ into a 20-bit column. The following complete finite calculation certifies the precise weight distribution of all binary sums of rows. It needs no claim about irreducibility or a BCH distance bound.

```python
from collections import Counter

def mul(x, y):
    z = 0
    for _ in range(7):
        if y & 1:
            z ^= x
        y >>= 1
        x <<= 1
        if x & 128:
            x ^= 0x83
    return z

def column(j):
    j2 = mul(j, j)
    j3 = mul(j, j2)
    j5 = mul(j2, j3)
    return 1 | (j << 1) | (j3 << 8) | ((j5 & 31) << 15)

cols = [column(j) for j in range(128)]
rows = [sum(((v >> i) & 1) << j for j, v in enumerate(cols))
        for i in range(20)]
word = 0
weights = Counter({0: 1})
for i in range(1, 1 << 20):
    word ^= rows[(i & -i).bit_length() - 1]
    weights[word.bit_count()] += 1
assert weights == {0: 1, 48: 10416, 56: 220416, 64: 586910,
                   72: 220416, 80: 10416, 128: 1}
```

The reflected Gray-code toggle visits each coefficient word once. The unique zero codeword gives full row rank; the nonzero minimum weight is 48. The enumerator is a deterministic finite Python check; formalization of this specific weight certificate is open.

### Why all balanced cuts must be wide

Let E be any set of 42 or 43 coordinates. If the restricted columns H_E span at most 16 dimensions in F₂²⁰, at least four independent linear combinations of the check rows vanish on E. Their four-dimensional span contains 15 nonzero words of weight at least 48, with aggregate weight at least 720. On at most 86 remaining positions a nonzero linear functional on that four-dimensional space is one on exactly eight of the sixteen words; a zero functional contributes nothing. Aggregate weight is at most 688, a contradiction. Thus rank(H_E)≥17. The complementary columns span all twenty dimensions, since any nonzero row combination vanishing there would have weight at most 43.

Define φ(w)=1 exactly when H w=0. Across the cut E versus its complement, acceptance is equality of the two partial syndromes. The endpoint can realize at least 2^17 distinct values and the complement can realize them all. Taking one representative on each side for each such value produces an identity minor over F₂. The proved Lean syndrome-minor theorem gives flattening rank ≥131,072. More generally, exactly the shared image syndromes contribute independent rows in the equality matrix. Every endpoint width in a representation u(x)B(z)v(y) bounds its corresponding flattening rank, and the dimension of the span of the middle matrices bounds the middle flattening rank. Consequently any exact representation at a 42/43/43 raw-variable split has both endpoint widths and middle span dimension ≥2^17. A literal full rectangular middle slice then has at least 2^34 binary fields. This does not lower-bound more succinct structured storage, circuit simplification, a witness reparameterization mixing different chunks, or arbitrarily unbalanced partitions.

### Registered NAND realization

Partition 128 inputs into 32 consecutive groups of four. Generate a lookup wire for each nonempty subset parity of a group: singleton wires already exist, while each other subset requires one XOR of its lowest singleton and the already generated parity of the remaining bits. This uses 11 XORs per group. For each of the 20 rows of H, take the nonempty group subsets selected by the row, combine them by at most 31 XORs, then negate the result. Join the 20 zero checks by 19 binary ANDs. Each XOR uses the four-NAND realization, each NOT one NAND, and each AND two NANDs. Even the unpruned bound is 4(32·11+20·31)+20+38=3,946 gates. Omitting empty groups in the actual matrix gives 3,530 gates. Insert unused NAND(true,true) gates before the original final gate, preserving all referenced wire numbers, to reach exactly 4,096. Direct registered-semantics evaluations agreed with the parity check on zero, all 128 unit inputs and 256 seeded full-length words. The network uses only backward reads. Zero is always a witness, and the linear predicate is efficiently decidable even if a target syndrome is added. The example supplies no hard SAT family.

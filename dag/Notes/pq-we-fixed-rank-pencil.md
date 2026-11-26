---
title: What rank-gap masking can transfer to a fixed challenge distribution
refs: [definition:WE_CircuitSAT, note:pq-we-rank-gap-lattice-barriers]
tags: [witness-encryption, reduction, rank, barrier]
---

Consider a proposed direct reduction that embeds a public matrix space derived from an NP statement into a fixed random matrix challenge by changing bases. Two distinct distributional questions arise. The first concerns the scalar outputs. The second concerns the public coefficients needed to simulate the ciphertext. They admit different answers even at maximum rank distance.

Let M_1,...,M_k be d-by-d matrices over a finite field of order q. Every nontrivial combination has rank at least R. Draw independent uniform field vectors s,r and reveal (s,y), where y_i=s^T M_i r. For a fixed s the output is exactly uniform on the image of the linear map in r. Its conditional distance to a uniform k-vector equals 1-q^(rank-k), where rank is that map's rank. The rank can drop only if s annihilates some nonzero pencil element on the left. Union bound over projective coefficient vectors gives total distance at most min(1, ((q^k-1)/(q-1)) q^-R). In a full-rank pencil the conditional image is the whole space whenever s is nonzero. The exact distance is q^-d (1-q^-k), independently of the pencil. This is a common comparison distribution for the scalar marginal and even permits s to be public. The argument uses fresh uniform r and supplies no simulation for encodings or auxiliary information correlated with r. In particular changing the short search vector of a rank-based WE scheme to a uniform field vector changes its witness decoder.

Even a full-rank pencil's public coefficients cannot in general be randomized to a single common law by invertible left and right multipliers and an invertible change of generator basis. Over F_2 take the two generators (I,T) acting on F_2^4. In one pencil T is multiplication by a nontrivial element of F_4 on two copies of F_4. In the other it is multiplication by a degree-four element of F_16 on one copy of F_16. Each of the three nonzero combinations is invertible in both examples. For any ordered independent generators X,Y of the transformed space, the degree of the minimal polynomial of X^-1 Y is respectively two or four. Indeed the left and right masks cancel up to similarity. Changing generators replaces the element t by (c+dt)/(a+bt) for an invertible binary coefficient matrix, which generates exactly the same subfield since the change has a fractional-linear inverse. Thus the two randomizations have disjoint support, witnessed by testing linear dependence of I, X^-1 Y and (X^-1 Y)^2. Identical dimensions and even identical complete rank histograms are insufficient to transfer the *public pencil*. The proof concerns this masking family only. The two pencils illustrate the algebraic hypothesis and are not claimed to be outputs of a particular CircuitSAT compiler.

A direct fixed-game reduction would need to generate statement-specific coefficients on the reduction side and embed the challenge in the remaining ciphertext, or justify a different way of sampling the public data. The scalar calculation gives an exact test of such an embedding for the uniform-vector marginal. For the bounded-vector ciphertext with witness correctness and correlated auxiliary encodings, the corresponding simulation remains open. No evasiveness implication, obfuscator or assumption about a statement-specific game is used in these calculations.

The listing exhausts all public rows, random vectors and ordered generator changes for both examples. Field elements are packed as binary polynomials.
~~~python
from collections import Counter
from itertools import permutations

def times_x(v, degree, modulus):
    shifted = v << 1
    return shifted ^ modulus if shifted >> degree else shifted

def small(v):
    return times_x(v & 3,2,7) | (times_x(v >> 2,2,7) << 2)

def large(v):
    return times_x(v,4,19)

def dot(x,y):
    return (x & y).bit_count()%2

for generator, quadratic in ((small,True),(large,False)):
    mats = [[v for v in range(16)], [generator(v) for v in range(16)],
            [v ^ generator(v) for v in range(16)]]
    for X,Y in permutations(mats,2):
        assert len(set(X)) == len(set(Y)) == 16
        ratio = [X.index(y) for y in Y]
        square = [ratio[ratio[v]] for v in range(16)]
        assert (square in [[(v if a else 0) ^ (ratio[v] if b else 0)
                            for v in range(16)] for a in range(2)
                           for b in range(2)]) == quadratic
        for s in range(16):
            hist = Counter((dot(s,X[r]),dot(s,Y[r])) for r in range(16))
            assert hist == ({(0,0):16} if s==0 else
                            {(u,v):4 for u in range(2) for v in range(2)})
print("two pencils, twelve generator pairs, 3072 scalar outcomes")
~~~

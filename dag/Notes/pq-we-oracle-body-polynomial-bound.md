---
title: A quadratic query bound for the secret slice in the WE stream body
refs: [definition:WE_CircuitSAT, note:pq-we-oracle-stream-body]
tags: [witness-encryption, quantum-security, complexity]
---

The preceding matrix-free body budgets three 128-bit WE header blocks at Q=2^60 quantum oracle queries. An acceptance-probability analysis reduces the requirement to two blocks under the same ideal-oracle and header assumptions. All data are classical except that the distinguisher may make coherent queries to the public body oracle. The game is a single challenge on a false statement with equal-length messages and fresh key randomness.

**Secret-slice game.** Carry out the preceding header switch separately for each message, at cost epsilon_header per endpoint, to obtain a dummy header independent of the real key. Set N=2^s. Fix an independent random oracle H and a separate independent table P of pad blocks indexed by counters. Use P to mask the challenge in all comparisons. For an auxiliary Boolean string X of length N define the public oracle to return P[i] on a valid query (tag,k,i) if X[k]=1, and otherwise H(query). At weight zero this oracle is independent of P. At weight one with a uniformly chosen marked position the resulting oracle is itself uniformly random, with its secret slice equal to the masking table. Thus these endpoints have precisely the distributions needed by the dummy-header comparison. Intermediate weights are auxiliary experiments. The simulation at any weight is a valid experiment even though multiple keys can share the same pads.

**Polynomial bound.** Fix H, P and the challenger's random tape independently of X. On the quantum query subspace indexed by a valid address (tag,k,i), the response-register unitary is (1-X[k]) times XOR by H(tag,k,i) plus X[k] times XOR by P[i]. On other addresses it is fixed. Every matrix entry is affine in X. After Q queries each amplitude has degree at most Q; each acceptance probability has degree at most 2Q, multilinearized on Boolean inputs. Intermediate classical measurements can equivalently be recorded coherently. Challenge generation using P, interaction, and prechallenge queries are included; only the Q oracle gates depend directly on X. Averaging over independent randomness preserves the degree. Symmetrize over strings of weight w. A monomial on j distinct positions averages to binom(w,j)/binom(N,j). The resulting real polynomial p(w) has degree D at most 2Q and takes values in [0,1] at each integer from zero to N. This uses the [quantum polynomial method of Beals et al.](https://homepages.cwi.nl/~rdewolf/publ/qc/polynomials.pdf).

For completeness put f=2p-1 and let M be its maximum absolute value on the entire real interval [0,N]. The rescaled Markov brothers' first derivative inequality gives sup |f'| <= 2 D² M/N. At a point attaining M the nearest integer is at most one half away and has |f|<=1. Hence M <= 1+D² M/N. For D²<N this gives |p(1)-p(0)| <= D²/(N-D²). Otherwise the trivial probability gap of one suffices. The two ideal games agree because the pad table is uniform and independent of oracle and prechallenge transcript. Summing the two endpoint differences gives the bound

    2 epsilon_header + min(1, 2 (2Q)² / (2^s - (2Q)²))

when the denominator is positive; use one for the oracle term otherwise. No chunk-count factor enters the polynomial degree. The header reductions still pay for their computation and their honest pad queries. This argument refines an upper bound; it does not prove the optimal key length.

**Parameter consequence.** For oracle contribution at most 2^-b it suffices that 2^s >= (2Q)² (1+2^(b+1)). At b=128 and Q=2^60 the smallest integer s satisfying this certificate is 252. A byte-aligned 256-bit key fits exactly two 128-bit WE encryptions and yields an oracle term below 2^-132. At Q=2^64 the same certificate requires 260 bits, exceeding two blocks. The revised 256-bit format has its own domain tag. Body size, chunk count and honest asymptotic costs remain the same as the prior oracle implementation. The result reduces the header ciphertext, encryption and decryption from three independent blocks to two in the former budget. It gives no certified security level for SHAKE256 as a concrete implementation or for the unresolved WE header. The full distinguishing target must also include the header terms.

The listing checks the exact minimum against the rational inequality at 256 query/loss budgets, verifies symmetrization on a one-query phase experiment, and checks nine byte-format round trips, including a 1 MiB message.

~~~python
from fractions import Fraction as F
from hashlib import shake_256
from math import comb
from itertools import combinations

def advantage(seed_bits, queries):
    N = 1 << seed_bits
    degree_sq = (2*queries)**2
    if degree_sq >= N:
        return F(1)
    return min(F(1),F(2*degree_sq,N-degree_sq))

def seed_length(queries, loss_bits):
    if queries < 1 or loss_bits < 1:
        raise ValueError("positive budgets required")
    needed = (2*queries)**2*((1<<(loss_bits+1))+1)
    return (needed-1).bit_length()

def transform(seed,body):
    if len(seed)!=32:raise ValueError("expected a 256-bit seed")
    result=bytearray()
    for offset in range(0,len(body),4096):
        i=offset//4096
        pad=shake_256(b'WE-body-256-v1\x00'+seed+i.to_bytes(8,'big')).digest(4096)
        result.extend(x^y for x,y in zip(body[offset:offset+4096],pad))
    return bytes(result)

def verify():
    for e in range(1,65):
        for b in (16,32,64,128):
            Q=1<<e
            s=seed_length(Q,b)
            assert advantage(s,Q)<=F(1,1<<b)<advantage(s-1,Q)
    for e in (60,64):
        print(e,seed_length(1<<e,128),advantage(256,1<<e))
    # A phase query on a uniform address followed by projection onto uniform.
    for N in (4,8,16):
        values=[]
        for w in range(N+1):
            mean=sum(F((sum(-1 if i in marked else 1 for i in range(N)))**2,N*N)
                     for marked in combinations(range(N),w))/comb(N,w)
            assert mean==F((N-2*w)**2,N*N)
            values.append(mean)
        for _ in range(3):values=[y-x for x,y in zip(values,values[1:])]
        assert all(x==0 for x in values)
    seed=bytes(range(32))
    for size in (0,1,4095,4096,4097,8191,8192,8193,1<<20):
        message=bytes(i%251 for i in range(size))
        ct=transform(seed,message)
        assert len(ct)==size and transform(seed,ct)==message
verify()
~~~

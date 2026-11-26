---
title: A fixed WE seed ciphertext and a length-preserving rounded-LWE body
refs: [definition:WE_CircuitSAT, note:pq-we-erasure-groups, note:pq-we-single-missing-position]
tags: [witness-encryption, complexity, correctness]
---

For a long message, encrypt a uniform s-bit seed using the existing WE header and XOR the message with a stream expanded from that seed. This standard hybrid-encryption architecture pays for WE only on the seed. Here is a public-parameter expander with an explicit quantum decisional-LWE interface and an exact per-ciphertext parameter budget. The underlying rounding technique is related to [Banerjee, Peikert and Rosen](https://web.eecs.umich.edu/~cpeikert/pubs/prf-lattice.pdf). The following simpler, publicly shifted estimator pays explicitly for its modulus-to-error ratio.

**Generator.** Let q=2^k, let 1 <= ell <= k, set D=2^(k-ell), s=nk and m=ceil(2s/ell). Sample once per ciphertext an independent uniform m by n matrix A modulo q and m independent public shifts z_i uniform in [0,D). View the state as n base-q digits x. For each row take the top ell bits of (A_i x + z_i) modulo q. Pack the row outputs in order, truncate to 2s bits, and split into an s-bit new state and an s-bit pad block. Iterate with the same A,z, emitting only the pad half. Truncate the final pad block to the public body length. The ciphertext contains the seed WE, A,z and the masked body. The decryptor expands the recovered seed with the transmitted A,z. A fresh independent seed is essential for each ciphertext. Correct seed recovery gives exact recovery for the entire body with no additional noise failures. For an s-bit header assembled from multiple WE blocks use its aggregate correctness and security budgets.

**Single expansion.** Assume quantum decisional LWE for exactly this uniform A and uniform secret with m samples, at modulus q and the specified error law. Let eta bound each error coordinate's expected absolute integer magnitude, independent of the freshly sampled shifts. Given an LWE challenge, append uniform shifts and round. Compared with rounding Ax, an error e changes coordinate i with probability at most min(1,|e|/D) over z_i for every fixed Ax and e. Indeed the residue within a rounding bucket is uniform and crossing a bucket boundary is necessary. This also handles modulus wrap. A union bound gives total statistical distance at most m eta/D. On the uniform challenge, even conditional on A,z, all rounded coordinates are exactly uniform because D divides q. Truncation preserves uniformity. The advantage between (A,z,G(x)) and (A,z,U_2s) is therefore at most epsilon_LWE + m eta/D for a single invocation. The matrix and shifts are public on both sides. This is a conditional statement; a large modulus chosen for the rounding estimate also changes the LWE hardness requirement.

**False-statement hiding.** First replace the encryption of the actual seed by WE encryption of a dummy seed. The reduction draws the real seed locally and can form the entire body for either fixed challenge message. Once the header is independent of the actual seed, replace generator calls in chronological order, incurring one single-expansion advantage per call. After replacing the earlier calls their pad blocks are uniform and their last state is uniform independently of A,z and the previous pads. A one-call simulator takes its challenge output as the current new state and pad, simulates the remaining steps with the same public matrix, and never needs the challenge input state. This justifies parameter reuse across iterations in this game. The final pad is uniform, and XOR hides equal-length messages exactly. For two real messages the distinguishing gap is bounded by 2 epsilon_header + 2 T (epsilon_LWE + m eta/D), T=ceil(L/s), with simulation overhead. All challenges and public transformations are classical and can be passed to a quantum distinguisher. No validity or integrity check on malicious ciphertexts is implied.

**Resource boundary.** For an L-bit body the raw size is C_header + m(nk+k-ell) + L bits, apart from framing. Enc and Dec each pay their seed-header cost plus Tmn modular multiply-adds, Tm shifts/roundings, and linear bit I/O. Enc also draws the public parameters once. For fixed security parameters the body work is linear in message length. For a target advantage, both hardness parameters and D must accommodate T; the stated size has polynomial overhead for polynomial parameters and message lengths. One cannot price the seed as a single 128-bit WE when nk is larger. The header's unresolved quantum hiding proof still applies. This route makes its own ordinary decisional-LWE parameter demand explicit.

**Accounting control.** At n=32, k=128, ell=16 and a 1 MiB body, the seed is 4,096 bits or thirty-two 128-bit WE blocks. The direct repeated-block route takes 65,536 such blocks. Fresh A,z add 263 KiB, with 33,554,432 modular multiply-adds per side beyond header processing. For eta <= 8 the cumulative one-sided statistical rounding term is 2^-89. These illustrative dimensions do not establish quantum security. Absolute savings depend on the header and on the parameter choices for both security reductions. The listing checks 10,932 exact boundary-crossing cases and 334 body round trips, including a partial last block, a nonaligned bit split, and empty messages. The reference packs the whole body in a Python integer; an implementation can XOR one output chunk at a time to obtain the linear I/O bound.

~~~python
from fractions import Fraction
from random import Random

def setup(n,k,ell,rng):
    width = (2*n*k+ell-1)//ell
    A = [[rng.getrandbits(k) for _ in range(n)] for _ in range(width)]
    shift = [rng.getrandbits(k-ell) for _ in range(width)]
    return A,shift

def expand(seed,A,shift,k,ell):
    n = len(A[0])
    s = n*k
    mask = (1<<k)-1
    secret = [(seed>>(k*j))&mask for j in range(n)]
    output = 0
    for i,(row,z) in enumerate(zip(A,shift)):
        y = (sum(a*x for a,x in zip(row,secret))+z)&mask
        output |= (y>>(k-ell))<<(ell*i)
    return output&((1<<s)-1), (output>>s)&((1<<s)-1)

def apply(seed,body,length,A,shift,k,ell):
    s = len(A[0])*k
    for offset in range(0,length,s):
        seed,chunk = expand(seed,A,shift,k,ell)
        take = min(length-offset,s)
        body ^= (chunk&((1<<take)-1))<<offset
    return body

def check():
    cases = 0
    # Exact crossing counts on all shifts, including bucket and modulus wrap.
    for k in range(2,7):
        q = 1<<k
        for ell in range(1,k):
            D = q>>ell
            for x in range(q):
                for e in range(-D,D+1):
                    mismatches = sum(((x+z)%q)//D != ((x+z+e)%q)//D for z in range(D))
                    assert mismatches==abs(e)
                    cases += 1
    rng=Random(945)
    trips=0
    for n,k,ell in ((1,3,1),(2,5,3),(3,7,4),(4,8,8)):
        A,z=setup(n,k,ell,rng)
        for length in range(5*n*k+1):
            seed=rng.getrandbits(n*k)
            message=rng.getrandbits(length)
            ct=apply(seed,message,length,A,z,k,ell)
            assert ct.bit_length()<=length
            assert apply(seed,ct,length,A,z,k,ell)==message
            trips+=1
    n,k,ell,L=32,128,16,8*(1<<20)
    s=n*k
    m=(2*s+ell-1)//ell
    rounds=(L+s-1)//s
    print(cases,trips,s,m,rounds,m*(s+k-ell),rounds*m*n,
          rounds*Fraction(m*8,1<<(k-ell)))
check()
~~~

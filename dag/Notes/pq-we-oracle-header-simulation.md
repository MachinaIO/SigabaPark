---
title: Simulating the independent body oracle in an ordinary WE header game
refs: [definition:WE_CircuitSAT, note:pq-we-oracle-body-polynomial-bound, note:pq-we-oracle-stream-body]
tags: [witness-encryption, quantum-security, reduction]
---

The previous matrix-free body proof used false-statement header hiding against an algorithm with an independent quantum random oracle. For an oracle-free header challenger and a dedicated finite body oracle, ordinary quantum header hiding suffices with an explicit increase in reduction time. The body remains in the ideal-oracle model. This is the bounded-query simulation principle from [Zhandry, How to Construct Quantum Random Functions](https://eccc.weizmann.ac.il/report/2012/140/), applied to the particular header switch.

**Direct simulation.** Consider a header switch on a fixed side of the two-message game. The reduction knows the true uniform seed K and requests a header challenge between K and a same-length dummy. It needs to serve Q quantum queries and make up to T classical pad queries. A (2Q+T)-wise independent function suffices. To see this, condition on each classical transcript, using unnormalized branch states. With response indicators I[x,y] for each oracle pair, a quantum query acts on a density matrix with degree increase at most two. A classical read at fixed x returning y contributes a single indicator on its transcript branch, including when the read address is determined by earlier measurements. Nonoracle channels are linear on the branch state. Summing transcripts gives an acceptance polynomial whose monomials involve at most 2Q+T distinct inputs. Their expectations match a random function, including repeated addresses or multiple contradictory indicators for one address. The two simulations therefore have identical acceptance probabilities. All initial advice and challenger coins must be independent of the sampled oracle. T is a public upper bound covering both allowed challenge messages.

**Preselecting the honest pads.** There is an alternative that avoids polynomial evaluation for the T honest pads. Before any adversarial query draw K, a uniform independent array P of T pads, and a 2Q-wise independent function F. For valid body queries (k,i) with k=K and i<T, return P[i]; otherwise return F(k,i). Use P directly to mask the body. For a truly random F, the patched oracle conditional on K is a random oracle, and the honest pads are exactly its values on the prescribed slice. Now condition on K and P: the comparison is between a truly random off-slice function and a 2Q-wise independent one. Only Q adversarial oracle queries are left, each adding at most two to the density-matrix degree in the off-slice indicators. The header challenge, even if it depends on K, uses no oracle and is part of the allowed oracle-independent computation at fixed K,P. The two averaged acceptance probabilities are identical on each side. The oracle is fixed coherently from the outset, including for queries preceding the challenge. Classical postchallenge mask generation may use fewer than T pads. No programming assumption or extra distinguishing term is incurred.

**Finite representation and time.** For a typed 256-bit seed and 64-bit counter the address has 320 bits. A 4 KiB block has 32768 output bits. Identify addresses injectively with elements of GF(2^32768) in a fixed public binary basis. Use the full field element as output. A random degree-less-than-D polynomial is D-wise independent by interpolation for distinct field elements (use a full random table if D exceeds the domain size). Fix a public irreducible modulus for field arithmetic. Horner evaluation takes at most D-1 field multiply-adds. A coherent evaluation computes the value, XORs it into the response and uncomputes the scratch. For the preselected variant a simple reversible multiplexor over T pads suffices to implement the exception lookup in O(T times the block-plus-index width) elementary gates per query. This circuit only simulates the dedicated typed oracle; if a game grants another unrelated oracle its simulation must also be specified. For Q=0 the off-slice circuit is unused.

Let R be the complete time of the ordinary quantum header reduction including randomness generation, reversible oracle evaluation, controlled pad lookup and the adversary. In the preceding proof replace epsilon_header by the ordinary header advantage at time R. The overall acceptance gap is still at most twice that advantage plus the prior secret-slice term. For polynomial Q and T this gives a polynomial-time reduction; the exact simulation does not establish a favorable concrete time loss. At Q=64,T=256 the preselected variant uses 512 KiB of polynomial coefficients and 1 MiB of pads. At Q=2^60 its coefficient storage alone is 2^73 bytes. These are simulator costs only. In particular the earlier 256-bit calculation at that Q numerically controls the body term but does not certify a 128-bit security level for the whole construction. Ciphertext size and honest Enc/Dec stay as in the prior body. The open quantum hiding step *inside* the lattice WE header remains.

The listing compares exact conditional pair distributions of a full random function and a patched affine family over GF(4), including repeated addresses, for all two-pad values and both keys. These 512 checks cover the one-query moments of the toy oracle. The general assertion follows from the degree argument.

~~~python
from collections import Counter
from itertools import product

def times(a,b):
    out=0
    for _ in range(2):
        if b&1:out^=a
        a<<=1
        if a&4:a^=7  # X^2+X+1
        b>>=1
    return out

def compare():
    field=range(4)
    full=list(product(field,repeat=4))
    affine=[tuple(times(a,x)^b for x in field) for a,b in product(field,repeat=2)]
    checks=0
    for key in range(2):
        for pad in product(field,repeat=2):
            fixed={2*key+i:v for i,v in enumerate(pad)}
            def answer(table,x):
                return fixed.get(x,table[x])
            for x,y in product(field,repeat=2):
                def counts(tables):
                    return Counter((answer(f,x),answer(f,y)) for f in tables)
                a,b=counts(full),counts(affine)
                assert a.keys()==b.keys()
                assert all(a[p]*len(affine)==b[p]*len(full) for p in a)
                checks+=1
    print("conditional pair marginals",checks)
    for Q,T in ((64,256),(1<<60,256)):
        # One field coordinate of 32768 bits fits every 320-bit address.
        ordinary=(2*Q+T)*4096
        programmed_poly=2*Q*4096
        pads=T*4096
        assert ordinary==programmed_poly+pads
        print("Q,T, polynomial bytes, pad bytes",Q,T,programmed_poly,pads)
compare()
~~~

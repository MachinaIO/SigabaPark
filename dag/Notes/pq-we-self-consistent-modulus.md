---
title: A self-consistent bit-length bound for correctness of the tensor WE encoder
refs: [definition:WE_CircuitSAT, note:pq-we-clocked-preimage, note:pq-we-compiler-transport]
tags: [witness-encryption, correctness, complexity]
---

In the [VWW matrix encoder](https://eprint.iacr.org/2022/1140.pdf) the previous level's public matrix times a sampled transition equals the next plaintext target plus fresh error, modulo q. With the clocked gadget preimage sampler in the linked note, increasing q also increases the width and the Gaussian error amplification. The following planner solves that feedback and selects the least prime-power exponent meeting the displayed residual bound for a supplied prime. This is an honest-evaluation bound. It does not choose parameters for evasive LWE, simulate the security hybrids, or fix noise flooding for security.

**Column amplification on every execution.** Use alphabet modulus q, H levels, Boolean transition matrices of logical width w, lattice factors of dimension n, and two branches. Let the integer tensor factors be bounded entrywise by S and all injected errors (including root noise) by E, with S,E>=1. These must bound the actual samplers at the noise widths used by the construction. For a centered scalar Gaussian implemented by the earlier shell sampler, t ceil(width)+1 suffices on every path, including timeout. For q-dependent flooding widths the planner below requires externally valid uniform caps or a separate analysis of their growth. Let m be the gadget basis dimension for rank nw. Give each of at most H setups precision lambda+ceil(log2 H)+3, and each of at most Q=2(H-1)m preimage columns precision lambda+ceil(log2(max(1,Q)))+3. Compute the setup width using setup precision, and the public Gaussian width sigma using column precision. This spends at most 2^(-lambda-2) on the combined public-matrix and conditional column approximations through sequential replacements when the old trapdoor is used only for these draws. Other noise laws and their implementation errors are separate.

For a fixed column x, the projection of x_final along Gram-Schmidt direction i is (z_i-c_i)||u_i||. The bounded scalar sampler has |z_i-c_i| <= t ceil(sigma/||u_i||)+1 including fallback. Since sigma >= ||u_i||, every projection has magnitude at most (2t+1)sigma. Orthogonality gives ||x||_2 <= sqrt(m)(2t+1)sigma. Thus ||x||_1 <= C=m(2t+1)ceil(sigma). This avoids passing through a potentially much larger bound on the intermediate residual during basis sampling. Reducing an emitted column modulo q preserves the modular identity with this short integer representative.

**Accumulating errors.** For a selected branch path let P_i be the ideal prefix row from a binary initialization vector (1-norm at most w) and i successive M tensor S factors. Each factor has maximum absolute row sum at most L=wnS, so ||P_i||_1 <= w L^i. The same estimate applies to each row of the full root. If the previous evaluated row is congruent to its ideal public product plus residual e, multiplying through the next selected block D gives residual eD + P_i E_next. The two contributions use different norms: the former uses maximum column 1-norm of D and the latter the previously bounded row. Therefore B_1=E and B_(i+1)=C B_i + w L^i E bound the absolute entrywise error before modular reduction. With q>=16(B_H+1) every such residual has an unambiguous centered representative, and a zero ideal terminal value passes the shortness test. The nonzero case uses independence, as detailed below. The inequality is simultaneous over paths when the entry caps hold.

**Solving for q.** At a trial q=p^j recompute the gadget digit count, matrix dimensions, error budgets, Gaussian width, C and B_H. Each is nondecreasing in j for fixed external inputs. If q is too small, jump to the least exponent giving at least 16(B_H+1) at the old B_H. Every skipped exponent necessarily fails its own test. At the first passing trial the returned j is minimal for this certificate. For k=ceil(log2 q), m, C and the precision parameters grow at most polynomially in k,n,w,H,lambda. The recurrence gives B_H <= E H w max(C,L,1)^(H-1). Hence log2(16(B_H+1)) is bounded by O(log(E+1)+log(Hw+1)+H(log(k+1)+log(nwH(lambda+1)+1)+log(S+1))). A polynomial bit length suffices since log(k+1) grows sublinearly (for example take a sufficiently large quadratic in the other input sizes, H and log2 p to absorb H log(k+1)). The first passing prime power has polynomial bit length, the jumps strictly increase, and integer arithmetic in the planner has polynomial bit complexity in these parameters. For fixed integer caps of polynomial bit length, ciphertext length is <= (2nm+2(H-1)m²)k payload bits per message bit. Encryption uses polynomially many bounded setup, column, tensor-target and noise operations provided the noise samplers themselves have polynomial clocks. Full-root decryption uses O(Hnm²) modular arithmetic operations plus reading the ciphertext, evaluating the witness trace and testing the terminal entries.

**A valid-witness correctness instantiation.** Suppose the frontend yields an all-zero ideal logical row for message zero and a unit message coordinate for message one, on every valid witness path. Use independent shifted-scalar draws with center zero and width 2 for the entries of the n by n tensor factors, with precision b_s>=5. This is an honest correctness choice; the security proof may impose different noise laws. For the ideal scalar law its normalizer is at most 1+2=3 by comparing the decreasing Gaussian on each half-line with its integral. The masses at 0 and 1 each exceed 1/8. The bounded sampler keeps both above 1/16; these values are distinct modulo any prime p. Every residue thus has probability at most 15/16. Set S = 2t_s+1 from the shell cutoff. If a row survives modulo p, the next row vanishes with probability at most (15/16)^n, by conditioning on all but a nonzero coefficient's entry in each independent column. Starting with the first standard row, a union bound gives failure at most H(15/16)^n. Choose n >= 16(lambda+ceil(log2 H)+2). For a surviving row and a unit logical coordinate, the ideal row has a unit entry modulo p^j. With an independent uniform terminal matrix its m coordinates are then independent uniform residues. Observed shortness implies the ideal entries all have centered distance at most 2B_H, even with correlated errors. This probability is at most ((4B_H+1)/q)^m <= 4^-m. Using the independent gadget setup as the terminal matrix adds its public marginal distance, at most 2^(-key_bits); the ideal-row event depends only on that public matrix and the tensor factors. Thus n as above and m>=lambda+2 give failure below 2^-lambda on each fixed valid path, and deterministic success on zero. This step does not compare the true preimage law to the ideal coset law, because the residual bound holds even on timeout. Honest errors may for example use centered scalar draws of a specified rational width >=1 with the corresponding shell cap E. The argument establishes a correctness regime; the corresponding parameters for message hiding remain open.

**Numerical checks.** With w=6, n=4, p=7, lambda=32, S=8, E=16, H=8 gives j=103, k=290, m=14022, and 798295456080 full-root payload bits per message bit. The next power-of-two exponent above the solution gives 1,523,155,484,160 payload bits. These are accounting controls with artificial caps and small lattice dimension; they are not security estimates. For 96 small parameter combinations an independent linear scan of every lower exponent verified minimality. Three additional two-level checks over bases 2, 3 and 7 ran the bounded column sampler from the preceding note, verified its 1-norm certificate, and checked the exact modular residual identity including both injected noises.

~~~python
from math import isqrt

def ceil_log2(x):
    return (x-1).bit_length()

def sqrt_up(x):
    return isqrt(x-1)+1

def account(H,w,n,q,lam,S,E):
    assert min(H,w,n,lam,S,E)>0 and q>=2
    k=ceil_log2(q)
    rank=n*w
    ell=rank*k
    # Provisional setup precision. Bound column error separately after m is known.
    key_bits=lam+ceil_log2(H)+3
    h=ell+2*(key_bits+ceil_log2(ell))
    m=h+ell
    Q=2*(H-1)*m
    pre_bits=lam+ceil_log2(max(1,Q))+3
    T=pre_bits+ceil_log2(m)+4
    sigma2=m*(ell+3)**2*T
    scalar_bits=T-3
    t=isqrt((scalar_bits+12)//4)+1
    # sqrt(m)*sqrt(m) times max projected error bounds column 1-norm.
    C=m*(2*t+1)*sqrt_up(sigma2)
    L=rank*S
    B=E
    row=w
    for _ in range(1,H):
        row*=L
        B=C*B+row*E
    payload=(2*n*m+2*(H-1)*m*m)*k
    return dict(k=k,m=m,C=C,B=B,payload=payload,Q=Q,sigma2=sigma2,
                fit=q>=16*(B+1))

def select(H,w,n,p,lam,S,E):
    # p is a supplied prime valid for the frontend; q=p^j.
    j=1
    while True:
        q=p**j
        a=account(H,w,n,q,lam,S,E)
        if a['fit']:
            return j,q,a
        needed=16*(a['B']+1)
        lo,hi=j,needed.bit_length()
        while hi-lo>1:
            mid=(lo+hi)//2
            if p**mid>=needed:
                hi=mid
            else:
                lo=mid
        j=hi
~~~

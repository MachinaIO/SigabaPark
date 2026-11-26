---
title: A fixed transition budget for published tensor WE via random-key smoothing
refs: [definition:WE_CircuitSAT, note:pq-we-vww-lossless-packing, note:pq-we-packed-columns]
tags: [witness-encryption, compilation, correctness, complexity]
---

The previous lossless codec occasionally uses the full residue size. The construction below instead emits a fixed public length on every encryption. It marks overflow and charges its probability to correctness. It works on the ciphertext distribution of [VWW Construction 4.2](https://ntt-research.com/wp-content/uploads/2023/01/Witness-encryption-and-null-iO-from-evasive-LWE.pdf), given the stated statistical implementation errors. The key estimate here supplies an all-target smoothing bound from a uniform public matrix, even at composite modulus. It does not require inspecting the trapdoor or restricting the target syndrome.

**Random keys.** Write A for a uniform r by m matrix modulo q, K its integer kernel modulo q, and s the width in the exp(-pi ||x||²/s²) convention. We bound the mean over A of the nonzero mass of the dual kernel with weight exp(-pi s²||v||²). The dual is Z^m plus the image of A-transpose divided by q modulo Z^m: characters of the quotient by K are characters of the image of A, and extend to the finite ambient group (equivalently, use Smith normal form). Sum over all y in (Z/q)^r to upper-bound that dual mass. The y=0 term after removing the origin is theta^m-1 with theta=sum_z exp(-pi s²z²). Repeated cosets in this sum can only enlarge the bound. In particular surjectivity is unnecessary.

For nonzero y of additive order d, a uniform column of A gives a uniform multiple of q/d as its inner product with y. Different columns are independent. The mean contribution of that coset equals the m-th power of (1/d) sum_j exp(-pi s²j²/d²), at most (1/d+1/s)^m by the decreasing Gaussian integral. There are at most d^r vectors of order d. For 2<=d<=s/2, sum the bounds (3/2)^m d^(r-m) over integers d>=2. For m-r>=3 the integral test gives at most 2^(r+1)(3/4)^m. For d>s/2 use at most q^r vectors and contribution (3/s)^m each. Finally theta<=1+4 times 2^(-4s²) for s>=1 by geometric summation. If 8m times 2^(-4s²)<=1 then theta^m-1<=8m times 2^(-4s²). The sum of these three bounds controls the mean nonzero dual mass. Markov bounds the chance of exceeding 1/3 by three times that sum. The integer certificate below rounds conservatively, using (3/4)^3<=1/2. A lower bound on s suffices for this part.

**Fixed-size WE.** For any key passing the dual-mass bound, the preceding coset-tail argument holds for every attainable syndrome, including adaptively selected ones, provided the column law given the key and target is the indicated coset Gaussian (or charged as an approximation). For N=2(H-1)m transition columns and u=lambda+1+ceil(log2 N), use C=ceil(sqrt(s_hi² m(m+2u+4))/2), where s_hi upper-bounds the width. Use the public fixed slots from the packed-column note. On a column exceeding its bit slot, send one overflow flag and a zero transition body of exactly the same size. Decryption on overflow can output zero. No overflow can occur when every centered column has 1-norm <= C. Thus the additional failure probability is at most

    2^(-lambda-1) + (H-1)(2^-v + delta_key) + delta_draw,

where v is the uniform-key certificate, delta_key bounds each public trapdoor matrix's distance from uniform and delta_draw bounds the accumulated conditional sampling error, including any bad trapdoors not covered by the sampler specification. Only H-1 keys are used for preimages. This bound is uniform in the original statement, witness and bit. Add it to the original valid-witness failure. Even on overflow the ciphertext is a deterministic public postprocessing of the original, so any distinguisher, including one testing the flag, transfers with exactly its original acceptance probabilities in both message experiments. This preserves any assumed backend hiding theorem. It does not establish the quantum hypotheses of that theorem.

**Bit budget.** For k=ceil(log2 q), the modeled VWW dimension m=2rk, r=nw, and slot length U from the packed-column note, the fixed payload is 1+2nmk+NU bits before public framing. For s of order sqrt(m), u=O(m), the transitions require O(log m) bits per coefficient. In the corresponding regime with growing k, k>=6 and s² bounded below by a positive constant times m, the key certificate v grows at least linearly in m for sufficiently large m. Choosing m large enough to absorb lambda and log H yields negligible uniform-key overflow. Statistical key-generation and sampler guarantees must still be charged at the desired precision. Packing adds polynomial honest computation and does not reduce the number of lattice preimage samples.

**Arithmetic control.** With H=8, n=32, w=8, q=2^128, s=1024 and lambda=128, the calculator gives m=65536, N=917504, v=21584, u=149, C=33631656 and Rice low-bit count 10. The full-root fixed payload is 722229002241 bits versus 7697118265344 raw bits per message bit. These parameters illustrate only compression and its statistical budget; they are not a concrete VWW security instantiation. A finite check at five small composite-modulus shapes verified the exact order-class averaging identity using rational periodic weights and exhaustive matrices. A further 1008 codec cases covered successful reconstruction and overflow, with 517 flagged. The reference code below assumes nonempty transition blocks (H>=2); for H=1 transmit the root directly.

~~~python
from math import isqrt

def ceil_log2(x):
    return (x-1).bit_length()

def smoothing_bits(rank,m,q,s):
    # Returns v such that a uniform key fails with probability <= 2^-v.
    # Integer-width certificate, allowing a vacuous bound of one.
    if m-rank<3 or s<6:
        return 0
    square=4*s*s
    if square<ceil_log2(8*m):
        return 0
    integral=square-ceil_log2(8*m)
    small=m//3-rank-1
    large=m*((s//3).bit_length()-1)-rank*ceil_log2(q)
    return max(0,min(integral,small,large)-4)

def fixed_bound(H,n,w,q,s_lo,s_hi,failure_bits,layout):
    assert H>=2 and n>=1 and w>=1 and q>=2 and 1<=s_lo<=s_hi
    rank=n*w
    k=ceil_log2(q)
    m=2*rank*k
    N=2*(H-1)*m
    v=smoothing_bits(rank,m,q,s_lo)
    u=failure_bits+1+ceil_log2(N)
    R2num=s_hi**2*m*(m+2*u+4)
    C=(isqrt(R2num-1)+2)//2
    slot,mode,b=layout(m,q,C)
    raw=(2*n*m+N*m)*k
    fixed=1+2*n*m*k+N*slot
    return m,N,v,u,C,b,raw,fixed
def fixed_pack(cols,q,C,layout,fields,bits_of):
    # The root blocks are transmitted separately. All transition columns have m rows.
    m=len(cols[0])
    slot,_,_=layout(m,q,C)
    body=[]
    for col in cols:
        if len(col)!=m:
            raise ValueError("inconsistent shape")
        try:
            body.extend(bits_of(fields(col,q,C)))
        except ValueError:
            return [1]+[0]*(len(cols)*slot)
    return [0]+body

def fixed_products(payload,row,q,C,N,layout,dot_from_bits):
    slot,_,_=layout(len(row),q,C)
    if len(payload)!=1+N*slot:
        raise ValueError("incorrect payload length")
    stream=iter(payload)
    if next(stream):
        return None
    return [dot_from_bits(row,stream,q,C) for _ in range(N)]
~~~

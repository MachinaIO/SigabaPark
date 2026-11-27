---
title: Joint polynomial parameter growth under an explicit quantum hardness envelope
refs: [definition:WE_CircuitSAT, note:pq-we-root-loss-budget, note:pq-we-explicit-table-decision-boundary, note:pq-we-quantum-prefix-tree]
tags: [witness-encryption, complexity, correctness, reduction]
---

An exponentially long proof table need not force exponential *honest* dimensions. [Vaikuntanathan, Wee and Wichs, Remark 5.1](https://ntt-research.com/wp-content/uploads/2023/01/Witness-encryption-and-null-iO-from-evasive-LWE.pdf) already use subexponential hardness and a polynomial modulus bit length for the binary construction. Here is an integer feasibility calculation with the actual alphabet sizes in the reduction. It prices simultaneous requirements under explicit hypotheses. The quantum evasive-LWE implication, the short-design LWE hardness at these dimensions, and concrete sampler errors remain premises.

**Hardness and wrappers.** Use common logical width w, H levels with B_i labels, prefix counts P_i, modulus q=2^K, rank parameter n=K^a for a fixed positive integer a, and m=2nwK. Thus n^(1/a)=K. Require the relevant quantum single-secret LWE advantages to be at most 2^-K up to time 2^K, at the required short designs with B_i n samples and modulus-to-error ratio; q/chi <= 2^K for chi>=1. Ordinary uniform-design LWE is interchangeable here only with an applicable design conversion and its own costs. Let S=2+lambda+H+w+n+m+K+max B_i. Assume the evasive hop at depth i<H has advantage and time multipliers at most 2^(c ceil(log2(S P_i))) for a fixed c, with additive errors accounted for separately. Assume each simulation outside these multipliers (including the isolated-tree wrappers) costs at most (S P_H)^e, including arithmetic on the chosen widths, for a supplied exponent e. These are interface bounds, not measured constants. Let g be the sum of the multiplier exponents. The full wrapper time for a test of time 2^lambda is bounded by 2^g (H+2) max(2^lambda,2^(e ceil(log2(S P_H)))). The per-depth isolated-tree hybrid count is at most J=w m H P_H by the suffix-product formula. Set u=lambda+g+ceil(log2(64H)). Checking K>=u+ceil(log2 J) budgets the computational terms for the two message comparisons with slack. The additive errors of the evasive assumption, implementation switches, and suffix purge still have to meet the weighted budgets; the check does not generate such guarantees.

**Flooding and correctness in the same search.** Assume centered independent tensor and late/fresh noise entries have variance at most n². Each Boolean reachable logical row has squared norm at most w. Uniformly over cuts the squared coefficients of the earlier statistical shift bounds are at most M=2 (max B_i) n m P_H w (n³)^H (H+1)n², including the factor from the Gaussian shift inequality. The isolated-tree sum has at most H terms, and the PRE shift concatenates B_(i+1) targets. Choose the last flooding width at least 2^u sqrt(M). Between successive proof widths insert a log gap at least ceil(log2(S P_i))², giving a superpolynomial ratio in S P_i. Only the first flooding width is used for honest root errors. This schedule assumes that the hop premise holds at the specified widths, including any required comparison to the late noise. Larger required gaps can be inserted and repriced.

For the correctness check assume a simultaneous tail event bounding root entries by z times the root width, tensor and late-error entries by zn, and absolute preimage entries by z times 2(1+floor(sqrt(nwK))). Then each preimage column has one-norm at most m times that cap. The ideal prefix row one-norm is at most w(n²z)^i on attainable logical rows. The listing propagates the residual bound through all H levels and checks q>=16(residual+1). Under that event this gives zero-message correctness. If independent tensor entries have mod-two atom bound at most 1/2, an initially nonzero row modulo two dies with conditional probability at most 2^-n at each multiplication. Hence a unit survives on the valid one path except with probability at most H 2^-n. With an independent uniform terminal key, a surviving row is short on all m columns with probability at most ((4 residual+1)/q)^m after allowance for the residual. Add key distance and the tail-event failure probability. The chosen z is a control value; a clocked sampler and trapdoor analysis must certify these bounds at the actual parameters.

**Why a polynomial K suffices for these inequalities.** For fixed a,c,e, log S is O(log K + log(2+lambda+w+H+max B_i)); log P_H is at most H log(max B_i). All log-time, advantage, flooding, and residual lower bounds on K above are polynomials in the input parameters and log K. In particular log of the column cap and log of n²z grow only logarithmically in K and the input parameters. Some polynomial K in those inputs eventually dominates all right-hand sides simultaneously, as does the next power of two. This argument also covers any explicitly supplied polynomial-in-those-logs gap, variance and sampler-tail budgets of the same form. Dense payload K(B_1 n m + sum_(i>=2) B_i m²), the number of preimage columns m sum_(i>=2) B_i and dense decryption n(H-1)m² are polynomial. Total honest bit time additionally requires polynomial-time key generation and clocked samplers. No explicit proof table is generated by these honest algorithms.

**Numerical control.** All three shapes have 2^24 logical paths. With w=24, lambda=64, a=2,c=1,e=2 the first passing powers of two in this schedule are:

| Levels and arity | n | Modulus bits K | log2 root flooding width | Accumulated multiplier bits g |
| --- | ---: | ---: | ---: | ---: |
| 24 binary | 17179869184 | 131072 | 113498 | 1587 |
| 12 four-way | 4294967296 | 65536 | 49825 | 726 |
| 8 eight-way | 1073741824 | 32768 | 28998 | 441 |

Grouping lowers accumulated hop loss and flooding gaps even at the same terminal path count. It requires a stronger sample-count interface per hop, with arity-dependent dimensions and suffix information. These are illustrative shape calculations under the supplied envelopes, not parameter recommendations, measured encryption times or proofs of quantum hardness. The listing uses integer arithmetic and never enumerates the 2^24 paths.

~~~python
from math import prod,isqrt

def lg(x):
    return (x-1).bit_length()

def plan(B,w,lam,inv_delta,hop_exp,sim_exp,gap_bits):
    H=len(B)
    paths=[]
    count=1
    for b in B:
        count*=b
        paths.append(count)
    for r in range(1,1024):
        K=1<<r
        n=K**inv_delta
        m=2*n*w*K
        scale=2+lam+H+w+n+m+K+max(B)
        gainbits=sum(hop_exp*lg(scale*p) for p in paths[:-1])
        unit=lg(64*H)+lam+gainbits
        # All costs below are in bits of loss or integer noise magnitudes.
        wrapperbits=sim_exp*lg(scale*paths[-1])
        timebits=gainbits+lg(H+2)+max(lam,wrapperbits)
        hybrids=w*m*H*paths[-1]
        if min(K-timebits,K-unit-lg(hybrids),n-lam-lg(H)-6)<0:
            continue
        var=n*n
        # Upper bounds for both isolated-table and PRE shift coefficients.
        U=paths[-1]*w
        moment=2*max(B)*n*m*U*(n*var)**H*(H+1)*var
        terminal_bits=unit+(lg(moment)+1)//2
        gap=sum(max(gap_bits,lg(scale*p)**2) for p in paths[:-1])
        root_bits=terminal_bits+gap
        z=lam+lg(H*m)+8
        pre_width=2*(isqrt(n*w*K)+1)
        col=m*z*pre_width
        residual=z*(1<<root_bits)
        for i in range(1,H):
            residual=col*residual+w*(n*z*n)**i*z*n
        if K<lg(16*(residual+1)):continue
        payload=K*(B[0]*n*m+sum(B[1:])*m*m)
        assert residual < (1<<K)//16
        assert timebits<=K and unit+lg(hybrids)<=K
        return (n,K,root_bits,gainbits,payload)
    raise ArithmeticError("search range exhausted")

for H,b in ((24,2),(12,4),(8,8)):
    print(H,b,plan([b]*H,24,64,2,1,2,8))
~~~

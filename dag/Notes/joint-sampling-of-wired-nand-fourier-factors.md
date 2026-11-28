---
title: Sampling a common phase after contracting adjacent NAND constraints
refs: [definition:WE_CircuitSAT_Capped, note:correlated-phase-guards-and-public-syndromes]
tags: [witness-encryption, fourier-analysis, finite-sampling]
---

## A bounded sampler that applies to every registered circuit

For a small block of NAND gates on d distinct, initially free wire indices, enumerate its valid Boolean assignments T. On v in (Z/4)^d compute the Gaussian integer P(v)=sum_{w in T} i^(-v·w). Orthogonality gives sum_v P(v)i^(v·w)=4^d 1_T(w) also for non-Boolean w. For each block j set K=4096, weights w_j(v)=ceil(K|P_j(v)|), total W_j, and H the least power of two at least 2 product_j W_j. The following procedure samples one common phase and one assembled vector; it never needs a satisfying assignment.

Draw a uniform integer below H. If it exceeds or equals 2 product W_j, set all v to zero and draw an independent uniform anchor phase U. Otherwise split it into one bit and a mixed-radix tuple of W_j-valued digits. Use the integer cumulative weights of each block to obtain v_j and the offset inside its interval. Conditional on this list the one bit and offsets encode a uniform index below 2 product_j w_j(v_j). Form z=product_j K P_j(v_j). Map |Re z| indices to the real sign of z, and |Im z| further indices to the imaginary sign; use an independent uniform fourth root on the surplus. The allocated slots fit since |Re z|+|Im z|≤sqrt(2) product_j w_j(v_j). This produces E[1_{v-list} i^U]=z/H; the independent uniform axis contributes zero, including the initial out-of-range case. The cost in fair random bits is at most log2 H+2. All ceilings use integer square roots, and all signs and radix operations use bounded integers.

Add the v_j entries for each shared wire modulo four into one public output vector. The constant-one reads, unavailable predecessor reads that the registered semantics defaults to one, and the final output pinned to one are folded into the anchor. Unused primary coordinates need no entry; one can equivalently retain zero entries there. Add U+2b to that anchor. At any normalized y with y_0=1 the first character is

    alpha · product_j 1_{T_j}(y restricted to its wires),
    alpha = product_j (K 4^{d_j}) / H.

Odd anchor three gives the conjugate at the negated frequency. Every odd term therefore vanishes on every unsatisfiable circuit and Fourier inversion gives exact equality of the complete two public laws. At every valid witness including its evaluated internal wires the scalar TV is exactly alpha, since the coefficient is positive real. No hardness assumption or implicit circuit-acceptance oracle is used. With exactly one complete accepting assignment and all free coordinates used, inversion leaves a single conjugate pair and the full ciphertext TV also equals alpha.

## Contraction before sampling improves the finite gap

First remove self-NANDs into unary blocks. Greedily form a maximal matching of remaining gates that share an actual normalized wire; use one common symbol for constant reads. Each unmatched nonunary uses three distinct wire symbols including its fresh output. These sets are pairwise disjoint in a universe of size at most 4225, giving at most 1408 unmatched gates. The streaming version keeps one pending gate per incident wire, clears a matched partner's three indices, and never reuses a matched gate. If two pending disjoint partners both overlap a new gate it suffices to take either; maximality only concerns the remaining unmatched gates.

Up to topological relabeling a matched pair begins with (0,1,2) and the distinct parents of the second gate are among 0,1,2,3 with at least one already present. This gives six unordered cases, with output a fresh symbol. For each of them, for a single gate and for unary NAND, count each squared Gaussian modulus and sum ceil(K sqrt(s)). The exact greatest ratios W/(K 4^d) are A=114907/65536 for a single, U=9889/8192 for a unary, and B=5038779/2097152 for a pair. For reproducibility, at the worst pair (0,1,2),(2,3,4), the histogram (s:count) is {0:109,2:284,4:196,8:88,10:148,16:40,18:32,20:56,26:28,32:10,34:16,36:4,40:8,50:4,64:1}. All local tables have at most 1024 cells.

There are r unary blocks and p pairs with 2p≥4096−r−1408. As B<A² and U²<B, the ratio of initial capacity to the numerator of alpha is at most 2 A^1408 B^1344. Comparing the numerator and denominator as integers gives ceil(log2(2 A^1408 B^1344))=2842. The numerator of alpha itself is a power of two, so every valid witness has scalar TV at least 2^-2842. A direct run with 4096 distinct-gate mixed wiring gave 2^-2614. For the unique all-ones AND instance with unary padding, the exact *whole packet* TV is 2^-1182. With independent three-wire blocks and the same common-phase method alpha at G=4096 was 2^-3320, and the independent fair-column construction on that instance had full TV 2^-6207. The new universal lower guarantee does not imply success 3/4, and the exact upper from the unique-witness example prevents that claim. An attacker or decoder may use the full public data; the unique-witness TV upper already grants access to all of it.

For a polynomial-time sampler in the usual arithmetic model each table is constant size, the products have O(G) bits, ranking uses bounded integer arithmetic, and the sparse final vector has at most two bits per wire plus anchor. Schoolbook arithmetic gives polynomial bit complexity. Parsing, tapes, clock and machine description in the registered model are not certified here.

## A limit for arbitrary correlations on an affine slice

For any law of a single mod-four vector F, put a(w)=E i^((u+Lw)·F) for w in (Z/4)^n. Suppose a vanishes whenever any w-coordinate is non-Boolean. Define f(v)=E[1_{LᵀF=v} i^(u·F)]; sum_v |f(v)|≤1 by the triangle inequality. Inversion identifies this sum with the average over independent fourth roots z_j of |P(z)|, where P is multilinear with Boolean-indexed coefficients a(w) (a conjugated grid is equivalent). For any complex A,B,

    E_{z in {1,i,-1,-i}} |A+zB| ≥ ((1+sqrt(2))/4)(|A|+|B|).

To check it, fix the relative angle and normalize the sum of magnitudes to one. The four-term average is convex in the first magnitude and invariant under interchange (conjugate the root grid after a rotation of the whole expression). It attains its minimum at equal magnitudes. The remaining average of absolute half-angle cosines is concave on each quarter turn between consecutive zeros of the summands, with equal endpoint values (1+sqrt(2))/4. Applying the inequality recursively to P=A+zB gives mean_{w Boolean}|a(w)|≤(2/(1+sqrt(2)))^n.

There is a 4096-gate registered circuit carrying the entire 128-dimensional slice: per primary input form n_i=NOT x_i and NAND(x_i,n_i)=1, AND the 128 ones using 254 NANDs, and append 3586 unary inversions. Every gate contributes to the final one. All Boolean trace wires are affine in the primary bits over Z/4 (wire n_i=1−x_i and the other gates constant); a non-Boolean extended input has a non-Boolean primary. Hence any law that eliminates all of these invalid slice modes has a valid witness with scalar TV≤sqrt(2)(2/(1+sqrt(2)))^128<2^-34.25. The bound also holds after taking an average over public seeds if each conditional law has the stated vanishing. The witness may be fixed after averaging over those seeds. General WE requires exact NO privacy but allows invalid modes on YES, non-projected decoding and unrelated auxiliary fields.

Nonlinear postprocessing, evaluating signed inverse-Fourier mass after many local frequencies collapse to one wired frequency, and publicly sampling that collapsed mass efficiently remain open. An issuer that has already decided SAT can trivially switch to a public payload on YES. The open issue concerns useful correctness on every circuit without such a decision or a comparable expensive preprocessing step.

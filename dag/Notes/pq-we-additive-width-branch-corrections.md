---
title: Additive width for binary-layer reversal with a shared gadget correction
refs: [definition:WE_CircuitSAT, note:pq-we-two-layer-reverse-view, note:pq-we-reverse-projected-preimages]
tags: [witness-encryption, construction, sampling, complexity]
---

Consider a chain over Z/q, q=2^k, with independent uniform keys A_i of shape n_i by m_i. A binary layer has transitions S_0,S_1 of shape n_(i-1) by n_i. Factor S_1-S_0=U V with inner dimension r (the trivial factorization allows r=n_i). Fix the transitions and basis error coins independently of the keys. The following modified wire format replaces the two independent full preimage banks of the preceding note.

For child A_i form W by the canonical k binary digits of every entry of V A_i, so G W=V A_i with G=I_r tensor [1,2,...,2^(k-1)]. Independently conditioned column by column for parent A_(i-1), sample H and K satisfying

    A_(i-1) H = S_0 A_i + E,
    A_(i-1) K = U G + F.

Publish H,K,W; K has only rk columns. On branch zero use D_0=H, and on branch one use D_1=H+KW. Then A_(i-1)D_1=S_1 A_i+E+FW. If E,F have entries at most B in absolute value, the effective error has entries at most (1+rk)B, using integer representatives before modular reduction. The same factor bounds effective preimage entries if H,K are bounded. This changes the original scheme, including its joint error law.

**Recursive reversal.** Given the child, generate W, draw [H K] as ambient Gaussian columns, and complete the parent from the two concatenated targets as in the one-layer reversal. Only m_i+rk columns require pivots. The sufficient width is

    m_(i-1) >= n_(i-1) + m_i + rk + slack_i.

The dyadic flatness estimate may separately require m_(i-1)>=2 n_(i-1)(k-1). Take the maximum of these two requirements, retaining an additional factor if required by the chosen Gaussian error budget. Starting with the terminal key, repeat upward; the distance for the full joint experiment is at most the sum of the one-layer bounds. To justify composition, replace layers from root to terminal: each replacement is uniform in the downstream data, and previously reversed ancestor kernels can be reapplied to the replaced joint law. The construction itself can run the reverse algorithm, without generating trapdoors. Count a missing pivot as an encryption failure. This statistical comparison only connects two samplers for this modified experiment.

**Cost and correctness scope.** The width bound is additive even using the trivial factorization. Each layer sends m_(i-1)(m_i+rk) Gaussian entries and rk m_i bits. For an integer cap C on the two sampled matrices, its Gaussian entries use ceil(log2(2C+1)) bits each plus a failure convention. Forward evaluation by a witness row x uses xH and, on branch one, (xK)W, in polynomial time. Reverse encryption uses ambient sampling, modular products and a pivot solve, all polynomial in the dimensions and k assuming polynomial-time approximate scalar sampling (add its joint distance). For h layers, writing E_i' for the effective branch error, the error in the product is exactly the sum of S-prefix times E_i' times D-suffix, in that order. If h<=L and all entry caps, transition integer lifts, ranks, key row dimensions, terminal width and slack are polynomial in L, choosing k=L² gives polynomial widths and an error bound 2^O(L log L) by submultiplicativity of the maximum row-sum norm. Thus error growth alone does not force superpolynomial bit length in this regime. A WE correctness theorem still needs an ideal endpoint decoding gap, probability bounds for these caps, and compatible security parameters.

**Exact disclosure introduced by the correction.** W reveals V A_i in full. For example, if V is public and has a public left inverse, A_i is recovered exactly. With an exposed projected parent R=P A_(i-1), the observer also obtains R K=P U G+P F and R H=P S_0 A_i+P E. On a noiseless correction the weight-one digit columns of R K reveal P U. Any pair of fixed message experiments with different such publicly recovered values is distinguishable. The two projected transition syndromes alone therefore need not suffice to simulate this compressed transcript. With public parameters common to both messages, an actual reduction must handle these disclosures jointly with the neighboring levels. The additive width removes the column-count recurrence, while secrecy of the new view remains open.

For an asymptotic statistical parameter example, take L growing, k=L², scalar width s=8L, all n_i>=1, slack 3L and parity-flatness threshold 2^(-3L) in the dyadic branch estimate. With polynomial dimensions, the union of key errors is at most poly(L) 2^(1-(k-2)+3L), the conditional parity and syndrome terms contribute poly(L) 2^(-3L), and the pivot losses at most L 2^(-3L). Here the scalar parity mass correction g^m differs from one by poly(L) exp(-Omega(L²)). In the reverse experiment preimage entries are ambient scalar Gaussians before any abort; a cap sL has failure poly(L) exp(-Omega(L²)) by summing the Gaussian tail. These choices yield negligible statistical and cap errors in this model without a hardness claim.

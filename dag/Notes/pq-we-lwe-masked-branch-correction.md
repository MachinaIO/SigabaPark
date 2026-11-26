---
title: A fixed LWE challenge hides the kernel component of a projected branch correction
refs: [definition:WE_CircuitSAT, note:pq-we-additive-width-branch-corrections, note:pq-we-reverse-projected-preimages]
tags: [witness-encryption, reduction, construction, complexity]
---

Consider the binary correction S1=S0+UV and the projected interface R=P A for a uniform parent A. Only R and the published banks expose this parent. Assume P has full row rank modulo two. Write C for the child key with m columns, U with r columns, and q=2^k. Choose a public r by a matrix Z satisfying P U Z=0 mod q. Its image may be any chosen submodule of this kernel, including one with no direct complement over Z/q. We blind the digit bank without publishing an unmasked V C. For the following local reduction all unmasked data are efficiently generatable independently of the LWE coins and parent, and any auxiliary outputs concerning them must also be included in the common view.

Sample uniform B of shape d by m, independent uniform T of shape a by d and independent LWE noise N of shape a by m. Write G_j for the j-row binary reconstruction gadget, and bits for its canonical right inverse. Set

    X = V C,   W = bits(X + Z (T B + N)),   L = bits(B).
    A H = S0 C + E,   A K = U G_r + F,   A J = U Z T G_d + Q.

Choose independent conditional Gaussian preimages for the three concatenated targets. Send H,K,J,W,B and the projected root. Compute L from B. Use H on branch zero and H+KW-JL on branch one. Gadget reconstruction gives precisely

    A (H+KW-JL) = S1 C + E + U Z N + F W - Q L.

Thus the short error budget gains at most ||UZ||_infty max-entry(N) from the LWE noise (maximum absolute row sum of the integer lift used in the product), plus rk max-entry(F) and dk max-entry(Q) from the digit products. The projected reversal now pools m+(r+d)k columns. Relative to the unmasked correction it costs dk extra parent columns and dm public residues, retaining additive width for fixed polynomial parameters. Noise rate, secret dimension and modulus must jointly give the desired LWE strength and decoding gap.

**Local hiding lemma.** Let delta be the uniform single-layer distance to the reverse projected sampler at this total width. Define a reference simulator taking the three projected targets P(S0 C+E), P(U G_r+F), P Q and the coset of each X column modulo image(Z), plus common auxiliary data and public dimensions and matrices. It draws independent uniform B and independent columns uniformly in the supplied cosets; it takes bits of those columns as W. It generates the integer preimage banks from their ambient laws and completes R using the projected targets (or aborts as in reversal). One can sample a coset by adding Z times a uniform vector to any representative. The target of J projects exactly to P Q.

For any quantum polynomial-time test the forward real view differs from this reference by at most delta + a epsilon, where epsilon bounds the single-secret decisional LWE advantage with matrix B, secret dimension d, modulus q, m samples and the specified scalar noise law, at the runtime of the reduction. First reverse the real sampler conditionally on all external and masking coins, including T. In this reversed projected law only W depends on the LWE rows given B and the external coins: no T is needed to simulate J or R. Replace the rows of T B+N one at a time with independent uniform rows using the same challenge B; other real rows can be generated with fresh secrets and noise. The uniform image under Z gives exactly a uniform coset. The challenger's distribution depends only on public size and noise parameters. Efficient sampling approximations add their joint distance. If comparing two forward views, apply this estimate twice and charge any difference between their reference inputs. External objects such as V or C that are themselves published must be included when comparing inputs.

The ciphertext itself determines X mod image(Z) columnwise from W, by applying the quotient map after bit reconstruction. In particular P U X is still exposed exactly. A witness path starting at P cannot see UZ through this correction; a different publicly obtainable incoming row P' with P' U Z nonzero would require simulating the secret-dependent target P' U Z T G_d+P' Q as well. Applying the local lemma at every layer independently is therefore unjustified. Even picking Z in the intersection of all reachable-row kernels would only mask corrections invisible to every such ideal row. A full WE proof needs a way to hide the remaining message-dependent view. The local result makes no assumption that a target statement is unsatisfiable.

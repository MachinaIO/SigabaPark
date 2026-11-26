---
title: Optimal header-assisted syndrome decoding and a total budget across YES targets
refs: [definition:WE_CircuitSAT, note:pq-we-optimal-cutoff-noise]
tags: [witness-encryption, coding, construction, complexity]
---

For a binary syndrome ciphertext write a=H^T s+e, c=s.y+mu, with uniform s independent of the noise. A witness Hx=y supplies d=c+a.x=mu+e.x. Every row of a binary matrix L with row space inside ker H yields the public noise check L a=L e. Take its l rows independent and let b_z=E[(-1)^(e.z)].

**Decoder.** Given j=L a, compute the Walsh sum
    F_x(j)=sum_(v in F2^l) (-1)^(v.j) b_(x+L^T v).
Predict e.x as zero for a nonnegative sum and one otherwise, then XOR with d. Orthogonality gives F_x(j)/2^l = Pr[L e=j,e.x=0]-Pr[L e=j,e.x=1]. Thus the success probability for either message is (1+B_L)/2 with B_L=2^(-l) sum_j |F_x(j)|. This is optimal among decoders of these statistics for an equiprobable bit. A basis of the entire kernel yields the optimum for the full ciphertext: conditioned on L e, the header is uniform in the corresponding coset of image(H^T), independent of e.x. For a small chosen subspace the sum costs 2^l coefficient evaluations per observed header, hence is polynomial for l=O(log n) when each coefficient is efficient. Adding checks never decreases the bias. If the full affine coset has a known enumerable list of nonzero coefficients, the full-kernel sum may instead be evaluated just on that list with characters (-1)^(a.(z+x)).

**Strict improvement with two checks.** Reuse the n=12, w=4 noise of the preceding note, whose biases at weights 1,2,3,4 are (3,3,1,1)/11. Let x0,x1,x2 have supports {1,2,3,4}, {1,2,5,6}, {1,3,7,8}, respectively. Choose H with kernel spanned by x0+x1 and x0+x2 and take y=Hx0. The fourth member x0+x1+x2 has weight six and bias zero. With x=x0 the Walsh sums are (3,1,1,-1)/11. The optimal full-header bias is 3/22, against 1/11 for every single witness here. Majority over independent decoded bits has squared-inverse-bias factor (22/3)^2 versus 121, a ratio of 4/9. Encryption and exact NO hiding are unchanged; this improves correctness for this matrix and target only.

**Across all target cosets.** Let Delta_y denote the total variation between one-ciphertext laws for messages zero and one at fixed H,y. For y in image H, Delta_y is precisely the full-kernel bias above, independently of the chosen solution x. Cauchy-Schwarz and Walsh Parseval give

    Delta_y² <= sum_(z:Hz=y) b_z²,
    sum_(y in image H) Delta_y² <= sum_z b_z² = ||f||_2²,

where f is the noise density relative to uniform. These inequalities allow arbitrary decoders, including unbounded ones with witnesses. If f has degree at most w then ||f||_2<=exp(w) by the previous norm estimate. For M distinct YES syndromes at the same H using the same noise law, some has Delta_y<=exp(w)/sqrt(M). For that y the variation on T independent ciphertexts is at most T Delta_y by coupling, even when the decoder processes all headers jointly. Thus constant advantage requires Omega(sqrt(M)/exp(w)) repetitions in the range where this bound grows. This latter argument needs only that the degree-cutoff law is common across y at this H. It permits dependence on H.

For example take H consisting of any positive number of copies of each of the n distinct unit columns. Every syndrome of weight w has a short witness, often many, giving M=binom(n,w) such targets. The bound is independent of the number of copies. Even with all public kernel checks and all redundant witnesses, column replication alone cannot yield a polynomial worst-case repetition count for n>=16w and w growing faster than log n, under the same cutoff. These duplicate-column instances are easy to decide; the example isolates the limitation of this encryption template. Statement-dependent choices varying with y, spectra supported on syndrome classes rather than a weight cutoff, and computational NO hiding require different arguments.

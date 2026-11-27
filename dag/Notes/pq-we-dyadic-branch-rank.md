---
title: An unchanged Gaussian preimage branch is invertible with constant probability
refs: [definition:WE_CircuitSAT, note:pq-we-uniform-syndrome-caps, note:pq-we-conditional-preimage-rank]
tags: [witness-encryption, sampling, reduction]
---

Consider a single unchanged branch with q=2^k, k>=3. Draw A uniformly of shape n by m mod q. Choose an arbitrary offset M of that shape, possibly depending on A, then draw fresh independent entries of E from the integer Gaussian of width sigma>=2 (weights exp(-pi x²/sigma²)). Put Y=M+E mod q. Given A,Y, draw each of the m columns of D independently from the product width-s integer Gaussian conditioned on Ax=y for that column. Count an unattainable syndrome as failure. On AD=Y an update to A that holds D and Y fixed must satisfy (delta A)D=0.

Set K=k-1, tau=s/2>=8 and m>=2nK. For b=2 exp(-pi tau²)/(1-exp(-pi tau²)) write g=(1+b)/(1-b). Pick a threshold h>0 with e=g^m h<1 and write H=g^m(1+e)/(1-e). Then

    Pr[D invertible mod q] >= 9/32 - 2^(1-n(K-1))/h
                             - (2^n-1)((1+1/sigma)/2)^m - m(H-1)/2.

**One exceptional set of keys for every parity pattern.** Reduce A modulo q/2 to B. For a centered width-tau Gaussian vector Z, the maximum relative syndrome deviation Delta(B) has mean at most 2^(1-n(K-1)) by the uniform syndrome estimate cited above. Discard keys with Delta(B)>h by Markov. Since h<1, the image of B is full, also modulo two.

For a product width-s Gaussian X, condition on X mod 2=r. Then (X-r)/2 has independent width-tau coordinates with centers -r_i/2. The width-tau normalizer for any real center c lies in tau(1 +/- b), by Poisson summation and a geometric tail bound. For any scalar frequency f, the modulus of the shifted characteristic function is at most g times the centered characteristic function: in the Poisson numerator discard phases to obtain the centered numerator, then compare normalizers. Thus every nontrivial Fourier coefficient of the shifted syndrome law has modulus bounded by g^m times its centered counterpart. The latter are nonnegative and their sum equals Delta(B) by inversion at zero (using coefficients normalized as expectations). All centered or shifted relative deviations are therefore at most e, simultaneously in r and in the syndrome.

The prior probabilities of the parity patterns have maximum/minimum ratio at most g^m by the same normalizer bounds. For a compatible r the remaining syndrome constraint is B((X-r)/2)=(y-Ar)/2 mod q/2. Multiplying its conditional probability by the prior and normalizing over compatible patterns shows that the posterior ratio is at most H. Each posterior point probability is within (H-1) times its uniform reference mass of that mass. Total variation is at most (H-1)/2 per column, and at most m times this for independent columns.

**Target rank.** Fix A,M. For any nonzero binary row v choose a pivot of v. Condition on the nonpivot entries of E. Each of the m constraints vY=0 mod two fixes the parity of a different pivot noise entry. Each atom has probability at most (1+1/sigma)/2 by the alternating-sum estimate in the syndrome note. A union bound over v gives the second error term. When Y has row rank n mod two, the uniform compatible column model has invertibility probability at least 9/32 by the conditional rank formula. Averaging over A,Y and charging the three errors proves the bound.

For example n=32, k=16, m=1024, s=32, sigma=8 and h=2^-155 give a bound above 9/32 - 2^-130. The exceptional key term is 2^-292. The target term is below 2^32 (9/16)^1024. Since exp(-pi tau²)<2^(-4 tau²), b<2^-1022 and g^1024<1+2^-1008, giving m(H-1)/2<2^-142.

Thus fresh Gaussian targets and conditional preimages can already pin down the parent, even when the offset is chosen using the public key. Marginal key distance and conditional sampler errors can be charged by coupling. These figures illustrate the single-branch model. Applying the estimate after conditioning on a descendant transcript requires controlling the resulting law. A reduction that jointly changes targets or their published preimages is outside the fixed-branch obstruction.

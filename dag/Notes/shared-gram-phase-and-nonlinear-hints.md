---
title: Shared Gram randomness, a nonlinear hidden syndrome and a three-trace barrier
refs: [definition:WE_CircuitSAT_Capped, theorem:AdvancedEncryption.WE.SharedBent.GramTarget, theorem:AdvancedEncryption.WE.SharedBent.SchurDecode, theorem:AdvancedEncryption.WE.SharedBent.AffineTriple, theorem:AdvancedEncryption.WE.SharedBent.SharedComplement]
tags: [witness-encryption, quadratic-phase, joint-distribution, affine-promise]
---

## A complete positive family

Work over F2. Suppose the public instance supplies a verified affine constraint system H w=c for its accepted witnesses. It suffices that every genuine witness satisfies the system and that it is inconsistent on every false statement in the promised class. The compiler below need not decide consistency or know a witness. The example gives actual 128-input, 4096-gate NAND statements. The method does not give such a system for arbitrary circuits.

Write h_i for column i of H and fix a public symmetric alternating matrix M0 whose image is contained in im H. Define the symmetric pencil

    M(w) = M0 + sum_i w_i h_i h_i^T.

Its diagonal is H w. For every binary symmetric M its diagonal belongs to im M: a kernel vector v has v·diag(M)=v^T Mv=0. For this pencil this also follows by squaring each scalar v·h_i and noting v^T M0 v=0. Thus at every satisfying w, c lies in im M(w), even when the pencil is singular. All inverses below can be any inner inverse J with M J M=M, calculable by elimination. Equivalently solve only the consistent systems needed to form the pairings. The diagonal-target Lean node formalizes the corresponding statement for arbitrary binary spaces via the dual quotient.

In a first issuer, draw independent uniform masks r,s of the row dimension. Publish the affine coefficient descriptions of

    F(w) = beta + r^T M(w)s + r·c + s·c,
    L(w) = M(w)r + c,           R(w) = M(w)s + c.

On a satisfying w return F(w)+L(w)^T J R(w)+c^T J c. Expanding and using c in im M proves that the answer always equals beta. In particular a bias amplified only up to a small constant is not being counted as correctness. On a false statement choose d with H^T d=0 and c·d=1. All M(w)d vanish, including M0 d by symmetry and the image hypothesis. The involution r to r+d fixes every coefficient in L and R and every nonconstant coefficient in F, and flips the unshifted anchor. Both message distributions on both full descriptions are exactly equal.

## A quadratic hidden phase that cannot be subtracted using public hints

For the second issuer draw a third independent uniform t. Put q(a,b,k)=ab+bk+ka. Publish all of H^T r, H^T s, H^T t, the constant terms M0 r and M0 s, and the affine coefficients of

    F(w) = beta + r^T M(w)s + q(r·c,s·c,t·c).

The variable coefficients of M(w)r and M(w)s follow from the disclosed scalar projections. On valid w compute a=w·(H^T r), b=w·(H^T s), k=w·(H^T t). Return

    F(w) + (M(w)r)^T J (M(w)s) + q(a,b,k).

Both quadratic contributions use the same underlying r and s that generated the public coefficients. The formula is correct on every outcome. At a NO, translate all three coins by d concurrently. The sides of the pencil, all slopes, and the whole third projection agree byte for byte. All three hidden target bits are complemented, and q changes by one. This is a full-view coupling with zero statistical error.

There is also a separation from merely appending a fixed publicly removable quadratic pad to an affine hidden phase. At a NO take the two coin directions that add d only to r or only to s. They separately fix every published hint and slope. The four-point mixed difference of the unshifted anchor in these directions is exactly one, from the ab term; the M0 term has zero mixed difference. Every function of the hints and slopes has zero mixed difference on that square. Subtracting any such function cannot turn the hidden anchor into an affine function of these original coins. This claim concerns these four coin points. It neither rules out nonlinear changes of hidden coordinates nor establishes difficulty of deciding the affine promise.

## One packet with many valid ranks and weak affine tests

Use 42 blocks of three primary variables (126 of the 128 slots). On an 84-dimensional base, the three columns in block j are e_(2j), e_(2j+1), and their sum. Embed the base by E(v)=(v,parity(v)) in 85 coordinates, applying E to each column. Let c=(ones_84,delta). The first 84 equations require each triple to be 110 or 001 in coordinate order; their column sums equal the two all-one coordinates in its block. Delta=0 gives 2^42 distinct active accepting assignments, and delta=1 gives a false instance by the dependent last row. (The two unused primary bits are free.) Equivalently c=E(ones_84) in the positive case. Choose M0=E D E^T with D the alternating matrix interchanging the first and second groups of 42 coordinates. This couples the same bank elements that appear in the variable terms.

Each paired pair of triple blocks has on the base the 4-by-4 form [[A,I],[I,B]]. Legal A and B range independently over I_2 and the all-ones 2-by-2 matrix T. Its rank is 2+rank(I+BA); it equals 2 for A=B=I and 4 otherwise since T^2=0. Embedding by E on both sides preserves rank. The very same issuer therefore supports each even legal rank from 42 to 84. For the first issuer the one projected zero-message bit has character magnitude exactly 2^(-rank M) on a valid w: summing over r imposes Ms=c, with probability 2^(-rank M); the residual character is constant on that solution fiber since c lies in the row space. Yet the joint decoder always succeeds.

Even allowing any affine Boolean test of the **full expanded coefficient packet**, one that includes the anchor has absolute correlation with the message at most 2^-42 on the true instance for both issuers. Omitting the anchor conveys zero message bias. Fix all coins except the first 42 components of E^T r and last 42 components of E^T s, which are independent uniform. The 42-by-42 bilinear cross block contributed by D is I. No choice of emitted slopes changes this block, since all h_i h_i^T terms are within one triple block. Any linear combination of the hint coefficients only adds linear terms. The majority version adds the all-ones outer product from (r·c)(s·c); its cross block is I+11^T, still invertible in even dimension 42. All other terms are affine on these remaining variables. Summing an affine-shifted invertible binary bilinear phase over one side proves the bound. This is a comparison with affine tests, not a computational hardness claim. The full classical nonlinear decoding succeeds in one evaluation with zero error. Unrestricted processing of these publicly decidable systems is easy.

The complete descriptions in this specific layout can be serialized more tightly. Send the one anchor bit and E^T r, E^T s, and, in the majority version, E^T t. Every slope and both M0 projections are deterministically computable from them. This gives respectively 169 or 253 bits before framing and uses respectively 170 or 255 uniform fair coin bits when sampling 85-bit banks directly. The raw coefficient lists above add no information to this serialization, but individual slope entries are bilinear computations of the compact hints. The affine-test upper bound was proved even with them exposed as extra coordinates. Computing the profiles and couplings uses binary operations; decryption may use elimination of an 85-by-85 binary matrix, or evaluate the displayed fixed base terms directly for the promise instance. No new cryptographic assumption or end-to-end registered-machine cost proof is asserted.

The promised true/false pair can be built literally out of NANDs: compute each of the 84 local XOR conditions with the four-NAND XOR macro. Form the parity of the 84 first and second bits by 83 XORs, select it or its complement according to delta, and conjoin all 85 bits with two NANDs per binary AND. Pad with pairs of self-NANDs; for an odd padding length at least three use z=NOT(value), u=NAND(value,z), NAND(z,u)=value once. All 4096 gates then feed the output. The compiler applies to this recognizable template or to a separately verified affine-system translation. Work counted for this promise is not a cost proof for the universal relation.

## A whole-view limitation for general coefficient pencils

For general public affine M(w), p(w), q(w), consider the raw complete affine coefficients of L=M^T r+p, R=M s+q, F=r^T M s+r^T q+p^T s+beta (the bit is in the constant coefficient). Write M_i,p_i,q_i for coefficients including i=0. For fixed full L,R, the two coin fibers are independent affine spaces r0+U, s0+V with U=intersection ker(M_i^T), V=intersection ker(M_i). Their contribution to all coefficients of F, beyond the offset at r0,s0, is precisely the **linear** image of (u,v) to (u·q_i+p_i·v)_i: every mixed term involving M_i vanishes. It is uniform on this image. Perfect concealment holds exactly if the anchor coordinate vector belongs to the image. Otherwise the two full laws have disjoint support, and elimination on the public descriptions constructs a decoder. The majority issuer is outside this raw affine-hidden-target prescription, as its mixed difference shows. It still uses an efficiently decidable affine input obligation.

## A restriction even for arbitrary nonlinear hints

For a raw affine trace response A(w)=U+V·w and any hint H, suppose for every genuine trace x one predicts A(x) from H with error at most epsilon. For any three such traces x,y,z, the XOR of their three predictors predicts A(x+y+z) with error at most 3 epsilon, by affinity and the union bound, with no independence assumption. Thus the TV between the joint laws of (A(x+y+z),H) and its anchor flip is at least 1-6 epsilon. This statement applies to arbitrary hint lengths, conditional laws and nonlinear predictors, including correlated shared-bank hints.

For a connected 4096-NAND true instance, put 64 pair tests NAND(x_i,y_i) first, fold their outputs by 63 consecutive NANDs, then apply 3969 NOTs. When all 64 test outputs are claimed to be one the fold ends at zero and the complete output is one. On this slice 3^64 of the 4^64 primary assignments give genuine traces. Every other raw trace on the slice is the XOR of three genuine complete traces: replace each illegal input pair 11 by 00,01,10 across the three traces and repeat every legal pair three times. All gate outputs of the three traces are identical throughout, so their XOR retains all claimed gate bits. With epsilon=2^-128 exact cancellation at all these illegal traces is inconsistent even with arbitrary nonlinear hints. This prohibits a pointwise clean-only Fourier design on this true statement. Ordinary WE demands indistinguishability on false statements and need not impose that pointwise cancellation. The positive issuer exploits precisely this distinction. Unlike a fixed invertible auxiliary Schur block, the legal generalized inverse here can change rank on the same statement; unlike a per-gate independent singularity hint bound, the final affine-hull restriction does not require linear hints.

Verification outside Lean included exact enumeration of both complete packet laws at a three-row binary instance, all 22 legal ranks and both payloads in the full-size instance, explicit bit-for-bit NO coin translations, and evaluation of the original full-size raw NAND circuits. The four formal nodes concern the Gram target, generalized Schur algebra, complemented majority and the three-trace identity. The universal capped construction and native clock obligations remain open.

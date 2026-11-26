---
title: Covering a 4096-gate CircuitSAT leaf with concrete box and modulus widths
refs: [definition:WE_CircuitSAT, note:pq-we-leaf-view-no-trapdoor, theorem:AdvancedEncryption.WE.CircuitSAT.leafCircuit_spec, theorem:AdvancedEncryption.WE.LeafView.zmodBox_abort_le]
tags: [witness-encryption, correctness, parameters]
---

Use the registered gate list unchanged, with the last gate as output. The theorem identifies its ring evaluation on every bit assignment with the registered Boolean result and bounds its noise by (W+1)^g E. It covers forward references with the primitive's default-true semantics. For a false instance, both the all-zero assignment and the chosen witness evaluate to zero, as required by the leaf-view lemma. This statement concerns circuit semantics and an error bound. A machine should operate on the shared gate list to avoid materializing its possibly exponential unfolding.

Here is a finite choice for the scalar leaf-coverage inequality in PR #43. Let q be any prime between 2^159999 and 2^160000 (Bertrand), n=1024, ℓ=128, k=160000, σ=2^320, mb=20971520358 and m=41943040358. Write W=nk=163840000, b=ℓW=20971520000 and M=(ℓ+1)m=5410652206182. Then m=mb+b. Let ET=σ(1+floor(sqrt(M))), E=(m+ℓ)ET and τ=W(W+1)^4096 E. Choose Bb=120000 and s=2^(Bb−1)−1−τ.

For an integer check without floating point, W+1 < 2^28, ET < 2^342, m+ℓ < 2^36, hence τ < 2^(28+28·4096+378) = 2^115094. Thus s is positive, 2^Bb ≤ q, and s + W errBound(W,E,φ) ≤ 2^(Bb−1)−1 for every translated circuit. The ratio of the omitted boundary width to the one-sided box radius is at most (τ+1)/2^(Bb−1); multiplying it by 2m still gives less than 2^-140. In particular m(4τ+1)2^140 ≤ 2^Bb. The accompanying zmodBox_abort_le theorem applies directly to boxSample over ZMod q: for any decomposition whose trapdoor shift has entries bounded by τ, a single try aborts with probability at most 2^-140. This bound is conditional on the shift bound, including the public ET check for the leaf application.

The same choice gives 24 M² b² < 2^158, b ≤ σ M, and mb−ℓnk=358. Hence the flooding shift across all columns is below 2^-162 and b sqrt(q^(ℓn)/2^mb) < 2^-144. These are statistical parameter checks. A WE security proof still needs the computational leaf and internal-node steps, and a concrete submission needs certified hardness and machine costs.

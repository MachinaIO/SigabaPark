---
title: Statistical message masking after the ideal succinct-LWE leaf switch
refs: [definition:SuccinctLWE, note:pq-we-tree-candidate-crux, theorem:AdvancedEncryption.WE.LeafView.succinctIdeal_augmented, theorem:AdvancedEncryption.WE.LeafView.uniformRow_masks_shift]
tags: [witness-encryption, leftover-hash, leaf]
---

In the registered ideal succinct-LWE law the public B and the uniform second component b form one uniform (n+1)-row matrix A. The extra row is indexed by none. The first theorem is an equality of the actual encoded instance laws, including the challenge trapdoor. The extra row b is public, as required by the seeded leftover hash lemma.

Consider t independent uniform binary columns r_i of length m. Give the continuation A, every B r_i, and the t masked values d_i + b r_i, where d is a fixed message vector. For any randomized continuation, changing d to d' costs at most t sqrt(q^(n+1)/2^m) in statistical distance. Apply the multi-column leftover hash lemma twice to A r_i. When all rows of the hashes are uniform, translating the spare row is a bijection that preserves all ordinary rows. The bound pays for n+1 output field elements per column, including the message pad.

In particular the continuation may draw W,T conditional on B and form further auxiliaries using A and the hashes it receives. For use in the full C1 hybrid, the reduction must produce exactly such a continuation from the encoded challenge and show that any published leaf keys or ciphertext components that depend on the original binary columns have this joint law. Matching the leaf-key marginal alone does not establish that property when the message pad uses the same columns. A concrete submission also needs a reduction machine and its cost.

With n=1024, k=160000, q<2^k, m=41943040670 and t≤m, the displayed cost is below 2^-300 because m−(n+1)k > 2(300+36) and t<2^36.

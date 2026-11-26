---
title: Statistical message masking after the ideal succinct-LWE leaf switch
refs: [definition:SuccinctLWE, note:pq-we-tree-candidate-crux, theorem:AdvancedEncryption.WE.LeafView.succinctIdeal_augmented, theorem:AdvancedEncryption.WE.LeafView.falseLeaf_message_mask]
tags: [witness-encryption, leftover-hash, leaf]
---

In the registered ideal succinct-LWE law the public B and the uniform second component b form one uniform (n+1)-row matrix A. The extra row is indexed by none. The first theorem is an equality of the actual encoded instance laws, including the challenge trapdoor. The extra row b is public, as required by the seeded leftover hash lemma.

Consider t independent uniform binary columns r_i of length m. Give the continuation A, every B r_i, and the t masked values d_i + b r_i, where d is a fixed message vector. For any randomized continuation, changing d to d' costs at most t sqrt(q^(n+1)/2^m) in statistical distance. Apply the multi-column leftover hash lemma twice to A r_i. When all rows of the hashes are uniform, translating the spare row is a bijection that preserves all ordinary rows. The bound pays for n+1 output field elements per column, including the message pad.

The formal joint view also contains a sampled key whose generation may read the original binary columns. The precise hypothesis says that for fixed A, any two binary inputs with the same ordinary hashes induce equal key laws. Choosing a representative of each attained hash fiber factors that law through the ordinary hashes, even when the message pad uses the same binary inputs. This choice is used only in a statistical proof. The continuation may draw W,T conditional on B and use further independent coins. For the actual false-leaf key, boxSample_eq identifies the whole conditional key law on each such fiber. The block identity and φ(w)=0 give B Rφ = EvalMat(φ,A_j), with A_j determined by the ordinary hashes and public setup. The statement keeps the setup and optional evalSim key in the same view as the masked row. The computational reduction still needs to produce this specified joint view from the encoded challenge and account for all additional ciphertext components. A concrete submission also needs a reduction machine and its cost.

With n=1024, k=160000, q<2^k, m=41943040670 and t≤m, the displayed cost is below 2^-300 because m−(n+1)k > 2(300+36) and t<2^36.

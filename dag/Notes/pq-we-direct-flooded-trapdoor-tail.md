---
title: Direct correctness bounds for the flooded trapdoor used by the leaf encryptor
refs: [definition:WE_EncryptorSetup, theorem:AdvancedEncryption.WE.LeafView.encryptor_leafGood_failure, theorem:AdvancedEncryption.WE.LeafView.challenge_none_le_setup_error]
tags: [witness-encryption, correctness, trapdoor-sampling]
---

Write M=(ℓ+1)m and b=ℓnk. In the encryptor's encLaw each of the b column samplers is present. Each column is an M-coordinate discrete Gaussian draw plus a correction whose entries have absolute value at most b. The correction may depend on that same draw. Pointwise, if every original entry has absolute value less than σ√M, the corrected entries have absolute value at most E whenever σ√M+b ≤ E. At σ≥1 the scalar Gaussian tail bound and a union bound yield

    Pr_encLaw[¬leafGood E T] ≤ 6 b M · 4^(−M).

This bound includes missing matrices and needs no smoothness, primality, or setup-replacement hypothesis. A separate support argument gives Pr_encLaw[T=none]=0 exactly, hence Pr_chalLaw[T=none] ≤ ε for any certified setup distance ε. The latter bound also applies to composite moduli whenever such a setup distance is available.

For example, M=5410652206182, b=20971520000 and σ=2^320 admit E=σ(1+floor(sqrt(M))). The required threshold can be checked exactly via E≥b and (E−b)^2≥σ²M. The direct tail is below 2^-140 since 6bM < 2^81 and 2M ≥ 221. These estimates apply before sampling the leaf key.

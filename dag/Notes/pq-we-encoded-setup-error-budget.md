---
title: Completing both succinct-LWE instances and budgeting the joint flooding shift
refs: [definition:SuccinctLWE, note:pq-we-encryptor-setup-flooding, theorem:AdvancedEncryption.WE.LeafView.floodingWidth_jointTheta, theorem:AdvancedEncryption.WE.LeafView.encodedLaw_close_of_setup]
tags: [witness-encryption, correctness, parameters]
---

Given a setup bound ε for (B,W,T), use the completion kernel that draws b from its conditional law given B and returns the registered encoding of (B,b,W,T). In the real world use the uniform secret and errorLaw. In the ideal world use the uniform vector. Conditional on B, the challenge can draw b before W and T as in lawWith. The encodedLaw_close_of_setup theorem proves that each resulting encoded distribution has the same bound ε against its corresponding challenge. Replacing both worlds in a difference of acceptance probabilities can therefore cost 2ε.

For the flooding calculation write M = (ℓ+1)m and b = ℓnk (in this paragraph b counts columns). The joint setup estimate charges the per-column shift term 2θ a total of b times, where θ = π M (b² + 2σMb)/σ². For positive b and σ, its exact contribution is

    2bθ = 2π M b³ / σ² + 4π M² b² / σ.

Consequently a shift budget δ > 0 requires σ ≥ 4π M² b²/δ. Under b ≤ σM, the accompanying theorem gives the sufficient condition σ ≥ 6π M² b²/δ. The radius condition in the setup estimate implies b ≤ σM. For example, assigning δ = 2^(−κ−1) to the joint shift within a single setup bound permits σ ≥ 12π M² b² 2^κ under that radius condition. The extra factor b compared with budgeting a single column adds log₂ b to the width estimate. The remaining Gaussian tails, smoothness and leftover-hash terms require their own shares of the setup error. The encoded-instance lemma introduces no extra factor of b.

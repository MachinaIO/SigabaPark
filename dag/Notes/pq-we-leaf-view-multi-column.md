---
title: Leaf lemma (C1) - multi-column leaf keys (gap 4 closed)
refs: [note:pq-we-leaf-view-no-trapdoor, theorem:AdvancedEncryption.WE.LeafView.leafView_close, theorem:AdvancedEncryption.WE.LeafView.leafView_close_multi, theorem:AdvancedEncryption.WE.LeafView.leafView_close_zmod_multi]
tags: [witness-encryption, lemma, trapdoor-sampling]
---
This closes item 4 ("several columns") of the gaps listed in `pq-we-leaf-key-exact-simulation` and
`pq-we-leaf-view-no-trapdoor`.

A matrix target `U = (U_1, …, U_L)` is preimaged one column at a time: the leaf key is the tuple of
`L` independent box-rejection tries (`Cslib.Probability.PMF.pi`), each with the same trapdoor.

* `leafView_close_multi` (any finite commutative ring) and `leafView_close_zmod_multi` (over
  `ℤ_q`, with norm-checked trapdoors): the real leaf view (attribute `0`, `A = B R`, no trapdoor
  for `B`) and the simulated view (attribute `w` with `φ(w) = 0`) with `L`-column keys are within
  the same bound as for one column, `2 · m_W √(|K|^n / 2^m) / 2`. The bound does not depend on `L`.

The proof is that of `leafView_close`. Each factor of the product is trapdoor-independent
(`boxSample_eq`), so the product is too. The view then reads only `B` and the hashes `B R`, and the
leftover-hash and shift argument is unchanged. The error does not grow with `L`: the keys add no
statistical distance, because their law given the public data is the same in both worlds.

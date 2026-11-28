---
title: "A unit-free binary projection with nearly disjoint share packets"
refs: [note:pq-we-binary-bilinear-full-view, theorem:AdvancedEncryption.WE.BinaryBilinear.character_cell]
tags: [witness-encryption, finite-distributions]
---

Partition 3m categories into three equal sets. Take the observation space R of vectors with the same parity in each set. Two independent parity differences give rank 3m-2, and no unit belongs to R. Its odd vectors form a nonempty affine projection. Nevertheless its two full projected bit laws have variation approaching one as m grows at fixed k.

Write q_j=<u_j,v_j>, and designate one anchor in each set. Each difference with its own anchor is an even row in R, so the public packet gives the two vector differences a_j,b_j and the dot difference q_j+q_0. They satisfy

    q_j+q_0+<a_j,b_j> = <u_0,b_j>+<a_j,v_0>.

The m-1 difference pairs in each set are uniform independent, by the bijection between private vectors and the anchors plus differences. An odd row on the three anchors publishes the sum of their u vectors, the sum of their v vectors, and the sum of their dot products plus the share. Whenever the difference equations and the two vector sums uniquely determine the anchors, the share is therefore determined by the full public packet. Uniqueness depends only on public unmasked coefficient rows, so it holds equally often in either world. The conditional supports on this event are disjoint.

Put h=2^(2k). Nonuniqueness requires kernel increments (d1,d2,d3) of length 2k each, not all zero, with sum zero. There are 3(h-1) triples with precisely two nonzero increments and (h-1)(h-2) with three. For each nonzero increment its m-1 independent coefficient rows give probability 2^(-(m-1)) of satisfying all homogeneous constraints. The class blocks are independent. Thus the distance is at least

    1 - 3(h-1)*2^(-2(m-1)) - (h-1)(h-2)*2^(-3(m-1)).

For k=65,m=131 the two error terms sum to strictly less than 4/2^130=2^-128. There are 393 abstract categories and rank 391. This information-theoretic example exhibits the need for rank or finer structure in full-view accounting. Realization as the projection of a particular registered NAND instance is open. No attack on a registry assumption or implemented cryptosystem follows.

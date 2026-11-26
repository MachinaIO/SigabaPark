---
title: Sampling all projected terminal preimages before their shared parent
refs: [definition:WE_CircuitSAT, note:pq-we-dyadic-branch-rank, note:pq-we-priced-endpoints]
tags: [witness-encryption, sampling, construction]
---

For the projected terminal level, pool all retained columns across labels into one m by t matrix. The following reversal samples their public integer preimages without a trapdoor, and supplies the shared parent for subsequent use. It works for arbitrary fixed targets Y of shape n by t. Auxiliary data and Y can first be sampled jointly, provided the forward parent is then uniform and independent of both. Take q=2^k and let G denote the centered product discrete Gaussian on integer m-vectors.

* Forward: sample uniform A of shape n by m. Draw independent columns d_j from G conditioned on A d_j=y_j modulo q. Return (A,D), with an abort for an empty fiber.
* Reverse: draw t independent unconditioned G columns D. Abort if D has column rank less than t modulo two. Otherwise choose A uniformly among solutions of AD=Y modulo q. To do this, select t pivot rows of D giving an odd determinant, sample the n(m-t) nonpivot entries of A uniformly, and solve for its pivot columns by modular elimination. The number of solutions is exactly q^(n(m-t)), independently of Y.

Here is an explicit joint-law bound. Assume that outside a set of forward keys of probability eta:

1. The syndrome masses p_A(y)=Pr_G[Ax=y] satisfy |q^n p_A(y)-1| <= u < 1 for every y.
2. A has full row rank modulo two and the parity law of a conditioned column is within v in total variation of uniform on its compatible residues, for every syndrome.

For t<=m-n the output laws, including abort, are within

    eta + (2^t-1) 2^(-(m-n)) + t v + 1-(1-u)^t

in total variation. To see this, on a good A write its parity matrix in coordinates [I 0]. In the compatible uniform model, the bottom m-n coordinates of each column are independent uniform bits. For any nonzero binary column combination, their sum vanishes with probability 2^(-(m-n)). A union bound and columnwise coupling give the two middle terms as a bound on forward pivot failure. On good successful pairs, divide the reverse point probability by the forward one. The G weights cancel exactly, leaving the product of q^n p_A(y_j) over all j. Its lower bound (1-u)^t gives the displayed result by summing the overlap of the probability masses. No flatness property of A conditional on reverse success is assumed.

For the dyadic Gaussian branch estimate in the cited note, the same good key suffices for both bounds: v=(H-1)/2, and the syndrome mixture over parity has an additional parity-compatibility factor. More precisely that factor is 2^n times the prior mass of the compatible parity classes, between g^(-m) and g^m (there are 2^(m-n) classes). Thus take **u=max(g^m(1+e)-1,1-g^(-m)(1-e))**. For n=32, k=16, m=1024, s=32 and t=64, the previous threshold h=2^-155 gives eta=2^-292, u<2^-152 and v<2^-152. The displayed distance is below 2^-144, uniformly in Y. This is an illustrative parameter calculation. No fresh-noise condition on the targets is required.

This reversal preserves the parent together with the entire projected block. Independent downstream coins may be appended using the same efficient conditional algorithm at no additional statistical cost. It specifically removes terminal conditional sampling in a simulator that can generate the rest given the new parent. Earlier encrypted levels that require its trapdoor, an already exposed function of its original coins, or a target that depends on this parent require further simulation. Pooling across labels matters: sampling a different parent per label changes the joint distribution. The method covers thin terminal blocks; at full interior width the pivot-failure estimate ceases to give a small loss.

**When the parent appears only through a root projection.** Suppose the rest of the public view uses A only through R=P A for a fixed l by n matrix P of full row rank mod two. In the reverse algorithm, conditional on successful D, R is uniform among solutions of R D=P Y. Indeed its nonpivot columns are independent uniform because P is surjective, and its pivot columns are then determined. One can generate (R,D) directly from P Y alone. In particular, two fixed target banks with equal P Y give identical reverse public laws and forward public laws within twice the displayed distance. Conversely R D=P Y is visible in the successful view, so different fixed projected syndromes are distinguishable there. This specializes the simulation to a projected layer and identifies exactly which target data a reduction for that interface must hide. The cost there is t independent m-coordinate Gaussian draws, one pivot elimination, and l rather than n rows of modular completion.

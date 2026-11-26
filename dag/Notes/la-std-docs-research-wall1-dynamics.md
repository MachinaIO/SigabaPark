---
title: "Equal covolumes give different conditional block minima"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall1_dynamics.md` (core v0.1.2).*

# Equal covolumes give different conditional block minima

The covolume-only transition proposed for the log-profile dynamics fails even for two consecutive exact block queries on a three-dimensional binary modular kernel. The observable that distinguishes the two histories is the next shortest length itself. Both histories have the same first shortest length, the same ambient determinant, and the same next block covolume. Only the first selected line needs to be recorded.

## Two overlapping blocks

Let the check row $(a,b,c)$ be uniform on the eight binary triples, and let $L$ be the kernel of the corresponding parity check on integer triples. Use a coordinate-adapted basis, meaning its first two vectors span the integer lattice $L\cap\{z=0\}$. Take block size two. In the first block choose an exact shortest line, breaking a tie between coordinate axes in favor of the first axis. Insert its primitive generator as the first basis vector. The second block is the projection of the whole lattice perpendicular to that generator, regardless of the basis completion.

Write $X,Y$ for selection of the first and second coordinate axes and $D$ for the second block covolume. The two conditional probabilities are

$$
 \Pr(\lambda_1^2=2\mid X,D=2)=1/3,
 \qquad
 \Pr(\lambda_1^2=2\mid Y,D=2)=1/2,
$$

where the minimum is that of the second block.

**Proof.** When $a=0$ the first unit vector is available and wins, including the tie when $b=0$. When $a=1,b=0$ only the second unit vector is available and it wins. When $a=b=1$ a diagonal of length $\sqrt2$ beats both axis generators of length two. This exhausts all first-block decisions relevant to $X,Y$.

On either axis event the selected vector has length one. Dropping its coordinate leaves precisely the two-dimensional parity kernel of the remaining row, since the dropped coefficient is zero. Its area is two exactly when the remaining row is nonzero, by the index formula. Among the three nonzero binary pairs, only $(1,1)$ excludes both unit vectors, and in that case a diagonal attains squared norm two.

Given $X,D=2$, the remaining pair $(b,c)$ is uniform on the three nonzero pairs. Given $Y,D=2$, the remaining pair $(a,c)$ is uniform on $(1,0),(1,1)$. The original histories have probabilities $3/8$ and $2/8$, respectively. Ordered remaining coordinate axes identify both quotient metric spaces isometrically with the standard Euclidean plane. This proves the claims.

## Consequence for conditional estimates

A single reference probability depending on dimension and covolume must err by at least $1/12$ on one of these histories, by the triangle inequality. The same bound applies in total variation to any common proposed law of the shortest length. The discrepancy enters at the tie decision. Selecting the second axis reveals that the check forbade the first unit vector. That check coefficient survives in the overlapping block. Conditioning on index two reveals only that the remaining check is nonzero.

For a deterministic horizon $T$, a valid substitute for independence would be conditional tail bounds. Let $F_i$ be block failure at step $i$, and let the history immediately before that step include all previous failures or successes. If on every surviving history the conditional failure probability is at most $p_i$, then the probability of any failure is at most $1-\prod_{i=1}^T(1-p_i)$, for deterministic $p_i\in[0,1]$. Indeed, conditional expectation of the next survival indicator on surviving histories gives a factor at least $1-p_i$ at each step. No fixed-block mean value alone supplies those conditional bounds.

This example addresses an exact transition law for the unplanted ensemble and the stated tie rule. Whether errors concentrate in large planted dimensions along a specified reduction trajectory remains open. Even control of the scalar profile would still require a joint estimate for the projected plant, including its primitivity and the absence of equally short or shorter competing lines.


## Independent audit (Nov 2026)

Verdict: **correct** (all eight check rows re-enumerated exactly). Scope check: breaking ties toward the second axis gives
the mirror image (1/2 vs 1/3); **breaking ties uniformly at random gives 2/5 for both**, so the discrepancy comes from the
deterministic tie rule. Covolume-only conditioning under symmetric/random tie-breaking, or approximately in high dimension,
remains open.

---
title: "What a bounded transcript tells us about the next minimum"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall1_information.md` (core v0.1.2).*

# What a bounded transcript tells us about the next minimum

Uniform tie-breaking removes the one-step discrepancy in the three-dimensional example of [wall1_dynamics.md](wall1_dynamics.md). After two insertions, even uniform tie-breaking gives different conditional laws at exactly the same covolume. The following example needs one binary check, four coordinates, and consecutive blocks of size two.

## Two histories with equal covolume

Let the check row be uniform on the sixteen rows $(a,b,c,d)$ over the binary field. Start with any basis of its integer kernel adapted to the standard coordinate flag (each prefix spans the intersection with the corresponding coordinate space over the integers). Visit basis positions $(1,2),(2,3),(3,4)$ in order. At each of the first two visits, choose uniformly among the shortest unoriented lines of the projected block, using fresh randomness, then insert a primitive generator by a unimodular change within the block. Write $H_{12}$ and $H_{13}$ for the histories selecting first coordinate axis 1 and then projected axis 2 or 3, respectively. Write $C$ for the terminal area and $E$ for the event that the terminal squared minimum is two. Then
$$
 P(E\mid H_{12},C=2)=2/5,\qquad P(E\mid H_{13},C=2)=4/9.
$$

Indeed, axis 1 wins only for $a=0$. If $a=1$, either axis 2 has a unit vector or a diagonal beats the length-two generator on axis 1. For $a=0$ the probability of axis 1 is $1/2$ if $b=0$ and one otherwise. On this history the next block is exactly the plane kernel of $(b,c)$ in coordinates 2 and 3. This follows because the first insertion preserves the span of the first three basis vectors over the integers, and dropping coordinate 1 imposes no further congruence. The same plane argument therefore applies to the second insertion.

In each history both deleted coefficients vanish, so the terminal lattice is precisely the plane kernel of the surviving two coefficients. It has area two iff that pair is nonzero, and among those pairs only $(1,1)$ gives $E$. The table lists the joint weights of each history and surviving pair, in units of $1/16$.

| History | Surviving pair | (0,1) | (1,0) | (1,1) |
|---|---|---:|---:|---:|
| $H_{12}$ | $(c,d)$ | 1/4 | 1/2 | 1/2 |
| $H_{13}$ | $(b,d)$ | 1/4 | 1 | 1 |

For the first row, $a=b=0$ forces a tie at the first visit. For the second, $a=c=0$ gives two ties if $b=0$ and two unique winners if $b=1$. Dividing the last entry by the row sum proves the formulas. Thus any common area-two reference law incurs TV error at least $1/45$ on one history, on a joint event of probability at least $5/64$. For uniform sampling of lines of length at most $s$ times the minimum, the same table holds for $1\le s<\sqrt2$: unit winners admit no longer competitor in that window, and a forbidden axis of length two cannot enter even when the shortest length is $\sqrt2$.

## Quantitative information bounds

Let $T$ be the full transcript, $Y$ the terminal observable and $C$ its covolume. All laws below are discrete, and information is in bits. Put $J=I(Y;T\mid C)$. Expanding the conditional mutual information gives the average over $(T,C)$ of the relative entropy from the posterior law of $Y$ to its law given $C$ alone. Pinsker's inequality and Markov's inequality therefore give
$$
 P\{\operatorname{TV}(P_{Y\mid T,C},P_{Y\mid C})\ge r\}
 \le (\ln 2)J/(2r^2) \quad(r>0).
$$
With at most $2^{b_i}$ choices at visit $i$, the chain rule bounds $J$ by $H(T\mid C)\le\sum_i b_i$. It gives no division by the entropy of the input. For example take $N$ independent fair bits, constant $C$, and let $Y=T$ be bit one. The TV distance is exactly $1/2$ on every transcript, however large $N$ is. For a lattice observable the four-coordinate example exhibits the same qualitative obstruction without encoding an arbitrary bit as the observable.

For rare events there is a different transfer bound. Form a reference experiment $Q$ with the same $(T,C)$ marginal and, independently of $T$ given $C$, draw $Y$ from its true covolume-conditioned law. For any event depending on all three variables with $Q$-probability $0<p<1$, its actual probability $x$ satisfies
$$
 x\log_2(1/p)\le J+h_2(x)\le J+1.
$$
Indeed the joint relative entropy to $Q$ is $J$. Grouping outcomes by the event via the log-sum inequality bounds it below by binary relative entropy, which equals $x\log_2(1/p)+(1-x)\log_2(1/(1-p))-h_2(x)$. Even here one needs the reference probability for the actual covolume-conditioned marginal. A fixed-subspace estimate does not identify that marginal.

Alternatively, if every possible transcript $t$ specifies a fixed test of the original random input whose bad event $B_t$ has unconditional probability at most $p_0$, the selected failure probability is at most $\min(1,2^{\sum_i b_i}p_0)$ by containment in the union of those events. This requires enough information in $t$ to specify the test, including its subspace. A short list of branch indices interpreted relative to an input-dependent basis need not specify any fixed subspace.

These bounds leave open concentration for the marked projected lattice of a particular high-dimensional planted ensemble. The finite example disproves general covolume-only conditioning under uniform ties. It supplies neither an asymptotic lower bound on the error in that ensemble nor a block size or running-time guarantee.


## Independent audit (Nov 2026)

Verdict: **correct** (exact rational enumeration of all 16 rows: P(H12, C=2) = 5/64 with conditional 2/5, P(H13, C=2) = 9/64 with
conditional 4/9; independent of the initial adapted basis; same values for s² = 3/2 and 1.99, changes at s² = 2 as the strict
bound predicts). Pinsker + Markov, `J ≤ H(T|C) ≤ Σ b_i`, the fair-bit example and the rare-event bound `x log(1/p) ≤ J + 1` are
correct. Wording: in the fair-bit example `T` is all N bits and `Y` is its first bit (`J = 1`); the table columns are labelled by
the surviving coefficients `(c,d)` and `(b,d)`.

Cross-reference (audit of wall1_coupling.md): in this 4-dimensional example the two histories have different in-block
Gram–Schmidt profiles, and conditioning on the full profile equalizes them. The obstruction is to covolume-only conditioning;
profile-only conditioning is not refuted by this example.

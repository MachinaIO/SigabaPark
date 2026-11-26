---
title: "What the Gram–Schmidt profile forgets during exact block reduction"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall1_profile.md` (core v0.1.2).*

# What the Gram–Schmidt profile forgets during exact block reduction

Even with one iid binary check and independent uniform shortest-line choices, the entire ordered profile can give the wrong conditional law for the next minimum. A forward width-three sweep exhibits this in dimension five. If the schedule allows revisits, dimension three suffices even when the predictor also knows the isometry class of the current block. Both witnesses use only selected unoriented lines as history. If a law depended only on the stated current data given a richer past, averaging over that past on each witness event would give the same conditional probability.

These are failures relative to the recorded-line filtration. They do not settle the weaker question of Markovianity when only successive scalar profiles are ever observed.

## A three-dimensional transition with identical current blocks

Use the Euclidean integer kernel of a uniform row $(a,b,c)$ modulo a prime $q=2$ or $3$. Query positions $[1,3],[1,3],[1,2],[2,3]$ in order. At each visit insert a primitive generator of a uniformly chosen projected shortest line, with fresh randomness. For a unit coordinate selection in a full block, put that coordinate first and complete by a coordinate-adapted basis of the residual kernel in increasing original coordinate order. This is a unimodular completion because the selected coordinate has zero coefficient and splits off as an orthogonal integer summand. Use any fixed adapted initial basis and any valid completion on branches outside the events below. “Select axis” here always means selecting its unit generator.

Consider first-two selections $(e_1,e_1)$ and $(e_3,e_1)$. Immediately before query three condition on the full squared Gram–Schmidt profile $(1,q^2,1)$. Since $a=0$, the second selection has restored the original coordinate order, and this profile is equivalent to $b\ne0$. Indeed the second spacing is the first admissible positive second coordinate, and for every third coordinate the congruence can then be solved in the second. The current block on both histories is exactly $\mathbb Ze_1\oplus q\mathbb Ze_2$. Its unique shortest line is unchanged by query three. The successor block is the kernel of $(b,c)$ in the last two coordinates. Its minimum exceeds one precisely when $c\ne0$.

For the repeated $e_1$ history, given $a=0,b\ne0$, the two selections have joint likelihood one if $c\ne0$ and $1/4$ if $c=0$. In the latter case the two unit axes tie both times. For the $e_3,e_1$ history, $c=0$ is forced and the likelihood is $1/4$. Thus the respective successor probabilities are
$$
\frac{4(q-1)}{4(q-1)+1},\qquad 0.
$$
For $q=2$ the conditioning events have masses $5/32$ and $1/32$. Any common predictor has conditional TV error at least $2/5$ on one of them. The projected block whose isometry class is supplied is the one at query three; of course the isometry class of query four itself determines its minimum.

Dimension three is minimal for this successor-isometry obstruction in the binary or ternary single-row model with a fixed schedule, standard coordinate-adapted initialization, Euclidean norm and a transcript of selected lines. In dimension two every proper block is a singleton, whose shape its spacing determines. Until the first full visit, singleton queries reveal only the fixed coordinate directions (a sign change has no effect). At a fixed schedule position the full-block law there is consequently its initial profile-conditioned law. After any full visit the first spacing is the minimum and the product of the spacings is the index. Singleton updates preserve both. These two numbers identify the full lattice up to isometry in this ensemble: index one gives the grid, and at index $q$ a zero coefficient gives a rectangle with minimum one. With both coefficients nonzero their ratio is $\pm1$ for either prime, giving a single isometry class by coordinate reflection. Repeated full visits have the same first spacing after insertion. Dimension one has only one spacing. This minimality statement concerns the stated schedule model; the dimension-three construction uses revisits.

## A forward sweep with no revisits

In dimension five visit $[1,3],[2,4],[3,5]$. On a unit selection keep the remaining coordinates of the visited block in their previous order and use their coordinate-adapted kernel basis. Equivalently, use an adapted basis for the reordered flag within the visited prefix. Such a block change exists because dropping a zero-check coordinate splits its unit summand, and the lattice spanned at the right endpoint is unchanged. On the histories below all deleted axes have zero coefficient, so orthogonal projection simply drops them.

Compare first selecting $e_1$, then $e_2$ or $e_4$. In the remaining ordered triple write the coefficients as $(r,s,t)$. At entry to query three the full squared profile $(1,1,q^2,1,1)$ is equivalent to $r\ne0$, by the same congruence argument. The terminal minimum exceeds one iff both $s,t$ are nonzero. Put $z=1$ if $s=0$ and zero otherwise. For the $e_2$ history the original row is $(0,0,r,s,t)$ and the two choices have likelihood $1/[2(1+z)]$. For the $e_4$ history it is $(0,r,s,0,t)$ and the likelihood is $1/(1+z)^2$. These are just reciprocals of the numbers of available unit axes at the two visits. The second surviving coefficient was examined twice on the latter history. The last coefficient stays uniform and independent.

| Prime | Uniform ties, second axis 2 | Uniform ties, second axis 4 | Lowest-index ties, second axis 2 | Lowest-index ties, second axis 4 |
|---|---:|---:|---:|---:|
| 2 | 1/3 | 2/5 | 1/4 | 1/2 |
| 3 | 8/15 | 16/27 | 4/9 | 2/3 |

For uniform ties, weight the $q-1$ nonzero values of $s$ against a zero value of relative weight $1/2$ or $1/4$, then multiply by $(q-1)/q$. For lowest-index ties the first history accepts every $s$ and the second requires $s\ne0$. For the uniform binary case the two conditioning masses are $3/64$ and $5/64$, giving a worst-history TV error of at least $1/30$. Conditioning the ensemble on a nonzero check changes none of the reported conditional predictions.

The accompanying Python enumerator sums exact rational probabilities over all rows, integrating the tie choices on the specified histories. It runs both schedules where they fit in dimensions 3–6 and both tie conventions. Extra coordinates append unit squared spacings since the prefix already spans the syndrome space. For the revisit experiment deterministic lowest-index ties give the second history zero mass. Reproduce with `python3 python/wall1_profile.py`.

## Consequences for conditional estimates

In the revisit example the single additional bit $[c=0]$ suffices to predict the binary successor isometry class exactly given the displayed state. For the general process an ordered basis Gram matrix, schedule position, and a completion and tie rule expressed in basis coordinates determine the transition with fresh coins: they specify every projected inner product, integer block coefficient and updated Gram matrix. Rules referring to ambient axes additionally need the corresponding coordinate data. Equivalently one can propagate a posterior on the hidden input and basis. Neither construction asserts that a smaller universal state is necessary. The audited fixed-column quotient law still applies to $t$ in the forward example. It supplies no uniform law for $s$ after the shortest-line choices.

The earlier four-dimensional width-two comparison remains consistent with this result: once the first surviving coefficient is known to be nonzero, only one fresh coefficient controls the terminal minimum there. In the anisotropically smoothed two-axis comparison of Part 18, the first residual squared spacing also identifies whether the first surviving coefficient is nonzero: it is the corresponding one-dimensional quotient metric entry times index squared (one or four), in disjoint spectral ranges even after scaling. If that coefficient is nonzero, the entire residual profile depends only on the metric and this index, and the last check bit remains independent and fair under either axis history. If it is zero and the area has index two, a unit survives. Thus on the common area interval the audited threshold event likewise has equal conditional probabilities within each profile stratum. This observation concerns that threshold, not equality of all smoothed shape laws.

The exact counterexamples leave open approximate bounds along a specified planted trajectory. Fixed-subspace probabilities and simultaneous flag counts would need to control the weight of the prefixes actually selected. For recovery one also needs the joint terminal event that the projected plant is nonzero and primitive and all competing lines are strictly longer. An unmarked profile transition, even if accurate in a particular regime, would not supply that probability.


## Independent audit (Nov 2026)

Verdict: **correct** (independent exact enumerator, brute-force shortest lines, profile computed directly). (a) q = 2: 4/5 vs 0
(masses 5/32, 1/32); q = 3: 8/9 vs 0; the current blocks coincide exactly; minimality of dimension 3 confirmed by brute force over
all schedules of length ≤ 5 in dimension 2 (7668 groups, no discrepancy). Caveat: (a) relies on the "restore original order"
completion rule fixed in the note; under "keep previous order" the second history's profile differs. (b) q = 2: 1/3 vs 2/5;
q = 3: 8/15 vs 16/27; lowest-index ties 1/4 vs 1/2 and 4/9 vs 2/3; no revisits. Script caveat: python/wall1_profile.py assumes
the pivot structure rather than checking the profile end to end (the audit's enumerator confirms it). Profile-only observation
(without selected lines) remains open.

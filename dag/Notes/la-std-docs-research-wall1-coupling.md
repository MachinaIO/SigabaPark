---
title: "Coupling fresh blocks along a reduction tour"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall1_coupling.md` (core v0.1.2).*

# Coupling fresh blocks along a reduction tour

Uniform independent tie-breaking does not in general make the next minimum depend only on block dimension and covolume, even for one uniform binary check, a fixed Euclidean metric and a left-to-right tour. There is also a separate support obstruction to comparing exact lengths with Haar lengths in total variation.

## Three successive width-two queries

Take the integer kernel of a uniform binary row $(a,b,c,d)$ in four dimensions, starting with a coordinate-adapted basis (each prefix spans the kernel intersected with the corresponding coordinate space). On blocks $(1,2),(2,3),(3,4)$ query the projected minimum, choose uniformly among shortest unoriented lines with independent tie coins, and insert a primitive generator, completing within the block. Record its projected line. Let $H_j$, for $j=2,3$, record first the line of $e_1$, then that of $e_j$, and terminal area two.

The first selection requires $a=0$: if $a=1$, either $e_2$ or a diagonal beats $2e_1$. For $a=0$ the probability of this selection is $1/(2-b)$. After it, projection drops the first coordinate; the next plane is exactly the binary kernel with row $(b,c)$ in the coordinate plane of $e_2,e_3$. Indeed the first insertion preserves the original rank-three prefix, and the dropped column is zero. The same plane argument requires the coefficient of the second selected axis to vanish. Conditional on availability its selection probability is one if the other coefficient is one, and one half otherwise. Dropping both axes gives the binary kernel of the remaining pair. Its area is two precisely for a nonzero pair, and its squared minimum is two precisely for the pair $(1,1)$ (otherwise a unit vector survives).

For each history the table gives the likelihood of its two selections for the three possible nonzero remaining rows. The remaining pair is ordered as $(c,d)$ or $(b,d)$, respectively. Each original row has prior mass $1/16$.

| History | $(0,1)$ | $(1,0)$ | $(1,1)$ | History probability | Conditional probability of squared minimum two |
|---|---:|---:|---:|---:|---:|
| $H_2$ | 1/4 | 1/2 | 1/2 | 5/64 | 2/5 |
| $H_3$ | 1/4 | 1 | 1 | 9/64 | 4/9 |

Both earlier selected lengths are one. Any common reference law for the last minimum incurs conditional TV error at least $1/45$ on one history, half the discrepancy. In expectation over histories these two events alone cost at least $(5/64)(2/45)=1/288$, by the triangle inequality with the smaller weight. Conditioning the original ensemble on a nonzero check also preserves both conditional probabilities. The asymmetry is temporal: the surviving coefficient $b$ in the second row of the table participated in both earlier contests. No tie coin is observed. The same table holds for uniform choice among primitive lines of length at most $C$ times the minimum, $1\le C<\sqrt2$: in either queried binary plane the next distinct length after the minimum is at least $\sqrt2$ times the minimum (unit axes, or diagonals in the odd-odd check). This example concerns histories recording lines; it does not separate two histories recording only the earlier scalar minima, or give an asymptotic lower bound in a planted ensemble.

## A fresh-block process and the comparison it permits

For definiteness start both processes with the same Gram–Schmidt length profile. Visit a deterministic list of blocks. For an ideal step with current block entries $g_i,\ldots,g_{i+b-1}$, put $D=\prod g_j$ over that interval. Draw an independent Haar unimodular $b$-lattice scaled by $D^{1/b}$. Take its HKZ basis (recursively insert a shortest projected vector, breaking ties uniformly among lines). Replace the interval by its successive Gram–Schmidt lengths, leaving the other entries alone. Lifts and signs do not affect these lengths. This is one explicit determinant-preserving model; even at the level of profiles its internal update is a modeling choice. The actual step may use its own block completion. For width two, both new entries are fixed by the inserted length and the area.

Write $K_t(h)$ for the actual conditional law of the emitted profile update given the observed past, and $M_t(h)$ for the fresh model kernel evaluated on that past's profile. Set $e_t(h)=d_{TV}(K_t(h),M_t(h))$. Couple emissions maximally while profiles agree, retaining the actual richer history for the conditioning; after the first disagreement continue each marginal normally. At step $t$ the probability of first disagreement is bounded by $\mathbb E_{\rm actual}e_t(H_{t-1})$, since the indicator of agreement so far is at most one (sample using fresh transition randomness). Summing gives an upper bound on path TV, capped at one. This proof also works with discrete reference kernels and with a final marked emission.

**Exact Haar error.** For an integer input and integer basis updates, squared projected lengths are rational: the orthogonal projector away from a prefix matrix $B$ is $I-B(B^TB)^{-1}B^T$. In each fixed rank $b\ge2$, a Haar minimum at any prescribed scale has no atoms. Indeed in local charts of $\mathrm{SL}_b(\mathbb R)$ each nonzero integer tuple $v$ has $\|gv\|^2$ a nonconstant real analytic function (stretch along $gv$ and compensate transversely); each level set is Haar-null. Take the countable union over tuples and descend to the lattice quotient. Thus conditional on the actual history including the profile, the fresh squared minimum lies in the rationals with probability zero and the actual minimum does so with probability one. For exact insertion the emitted first length alone gives **$e_t=1$ at every rank at least two**, including the first draw. Rank one has zero length error. Binning lengths would remove this support argument but requires new bounds on the bin probabilities.

**Discrete reference.** A fixed, previously unexamined coordinate block of an iid prime-field check has an exact replacement conditional on the preceding columns: project its fresh columns into the syndrome space modulo the span of those preceding columns. They are independent uniform quotient columns, and solvability for the omitted coordinates is precisely vanishing of their quotient syndrome. This gives zero error for that matched block law, also after conditioning both laws on the same positive-probability determinant event. For a fixed region the usual first moment follows by summing membership probabilities: for a nonzero residue tuple each of $r$ independent uniform checks vanishes with probability $1/q$, giving $q^{-r}$, while zero residues always pass. Such counts bound presence probabilities by Markov's inequality. They do not give conditional TV after a shortest-line selection. The table quantifies this limitation even allowing an arbitrary common discrete reference. Neither the fresh-column identity nor its zero error automatically survives conditioning on a short plant.

## Terminal marking

A model on profiles alone has no plant. One explicit extension at the last fresh block is to draw a primitive unoriented line uniformly among those of generator length at most a prescribed $R$, recording a null mark if there are none. With $N_R$ the number of such lines, a single line guarantees success. In fact for Haar rank at least two the model success probability is $\mathbb E[\mathbf1_{N_R>0}/\max(1,N_R)]$: distinct primitive lines almost surely have unequal lengths by the same analytic level-set argument applied to the difference of their squared lengths (stretch in a direction where their squared components differ). The mark is a model assumption. For the actual block, success requires a nonzero primitive projected plant and no other line with generator length at most its norm. Include the success indicator with the terminal emission in the coupling above. The actual success probability is at least the displayed model probability minus the summed errors for these joint emissions, by agreement on coupled paths. Matching unmarked marginals alone supplies no terminal mark error estimate.

For exact Haar replacement the bound is vacuous already at the first nonsingleton block. For discrete or rounded replacements, controlling the selected planted histories and their terminal marks remains open. These calculations certify neither a block size near 406 nor a running time for achieving recovery.


## Independent audit (Nov 2026)

Verdict: **sound, with one interpretive correction.** All numbers reproduce (H_2: 5/64, conditional 2/5; H_3: 9/64, conditional
4/9; TV bounds 1/45 and 1/288). Claims 2 (Haar replacement has TV error 1: rational vs almost surely irrational minima) and 3
(path coupling, terminal mark, discrete reference for fresh coordinate blocks) are correct; the model's success criterion differs
from the actual one, and the discrete reference holds only while the block is unexamined.
**Correction to Claim 1:** the two histories differ in their Gram–Schmidt profiles. Conditioning on the in-block profile entries
removes the discrepancy (terminal squared entries (1,4): probability 0 under both histories; (4,1): 1/2 under both). So the example
refutes conditioning on dimension + covolume only; it does not show dependence on recorded lines beyond the profile, nor a temporal
asymmetry. A reference that uses the full in-block profile has zero error here.

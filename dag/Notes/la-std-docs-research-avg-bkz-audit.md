---
title: "Audit of the coordinate flag in a random modular kernel"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/avg_bkz_audit.md` (core v0.1.2).*

# Audit of the coordinate flag in a random modular kernel

**Verdict.** The projection law, the conditional Gram–Schmidt law, and the integer-grid obstruction hold for an iid uniform matrix over a prime field and a coordinate order independent of the matrix. The qualification on the ensemble matters even before reduction. [Note under review](avg_bkz.md)

## Projection and its conditional law

Fix the entire prefix matrix $P$, put $S=\\operatorname{im}P$, and write $k=d-t$. A suffix $y\\in\\mathbb Z^k$ lifts exactly when $P\\bar x=-B\\bar y$ is soluble over the field, since each field solution has an integer representative. This gives the kernel of the quotient matrix on integer suffixes, including when $S=0$ or $S=\\mathbb F_q^n$. The eliminated lattice contains $qe_i$ on each prefix axis, so dropping those axes realizes Euclidean projection onto the orthogonal complement of its span.

Given $P$, each prescribed tuple of quotient columns has $|S|^k=q^{rk}$ antecedents among $q^{nk}$ equally likely tuples. Its mass is therefore $q^{-(n-r)k}$, the product law of fresh uniform columns. A quotient basis fixed given $P$ identifies this with iid field entries. Conditioning the *whole* matrix to have full row rank would change this calculation. For example, with $n=d=1$ that conditioning forces the first column to be nonzero.

## Gram–Schmidt lengths

Let $L_t$ be the kernel supported on the first $t$ axes. Projection onto the last of these axes has kernel $L_{t-1}$. Its image consists of the integers $a$ such that $a[c_t]=0$ in the quotient by the previous column span. Its positive generator $g$ is one for a zero class and $q$ for a nonzero class, using primality. Adjoining any lift of $g$ to a basis of $L_{t-1}$ gives a basis of $L_t$ by division in $g\\mathbb Z$. Its orthogonal residual is $ge_t$, since the earlier vectors span the previous coordinate plane. Given previous rank $r$, the probability of length one is $q^{r-n}$ and that of length $q$ is $1-q^{r-n}$. As a determinant check, the product through step $t$ is $q^{r_t}$, the index of $L_t$ in $\\mathbb Z^t$. The rank changes with the observations, so these conditional probabilities do not assert independent lengths.

## When the suffix is a grid

For $t\\ge n$, counting independent rows gives the exact probability of full prefix rank as $\\prod_{i=0}^{n-1}(1-q^{i-t})$. Each line of left annihilators survives with probability $q^{-t}$, giving the stated union bound on failure. Full prefix rank suffices for a grid. Rank deficiency can also yield a grid if every suffix column lands in $S$, an event of conditional probability $q^{-(n-r)k}$. Near-certainty follows when the failure bound is small, for example as $t-n$ grows at fixed $q$.

On the grid event a unimodular suffix basis change preserves the set of Euclidean points. In particular, every squared norm remains integral. At the terminal radii of the cited construction, adjacent even suffix dimensions with the same $\\lceil\\ln k\\rceil$ have squared centers separated asymptotically by $4/(3\\pi e)$, while both squared intervals have width $O(1/k)$. Both intervals cannot contain integers for sufficiently large such pairs. Choosing $d-t$ from the resulting empty-shell dimensions establishes the obstruction; it requires no claim about every suffix dimension. [Block geometry, S1 lower](reverse_minkowski_blocks.md)

## Lean evidence and remaining scope

Checking the source with `lake env lean SigabaNeoStd/Lattices/Reduction/AvgBKZ.lean` succeeded. Both axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The theorem `coordinateProjection` is a pointwise solvability equivalence for a surjective map into the prefix domain, a linear map, and a fixed syndrome. Substituting integer reduction, $P$, and $B\\bar y$ gives the required membership test for each $y$. The theorem `quotientColumnCount` computes the natural cardinality of one tuple fibre as `Nat.card S ^ k`. Its probability interpretation uses the finite uniform ensemble above. These declarations formalize the two algebraic steps claimed in the note. The orthogonal identification, probabilistic specialization, Gram–Schmidt calculation, and shell obstruction are paper deductions. [Lean source](../../SigabaNeoStd/Lattices/Reduction/AvgBKZ.lean)

The law of a prefix selected by a BKZ tour and the conditional position of a planted vector remain unverified. This audit establishes no tour or runtime bound.

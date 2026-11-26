---
title: "A coordinate flag in a random modular kernel"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/avg_bkz.md` (core v0.1.2).*

# A coordinate flag in a random modular kernel

Consider an iid uniform parity-check matrix over the prime field of size
$q$, with $n$ rows and $d$ columns. Its integer kernel modulo $q$ is $L$.
Choose the coordinate ordering independently of the matrix. After $t$
coordinates write the matrix as $[P\ B]$, let $S$ be the column space of $P$,
and let $r$ be its dimension. All probabilities below refer to this ordinary
matrix ensemble. Module structure and planting can change the law.

**Single projection.** Conditional on the entire prefix $P$, dropping its
coordinates from $L$ gives exactly the integer modular kernel of the columns
of $B$ reduced in the quotient by $S$. Indeed a suffix $y$ lifts precisely
when $-By$ is in $S$, since every residue prefix has an integer lift. Each
tuple of $d-t$ quotient columns has exactly $q^{r(d-t)}$ lifts to columns in
the original syndrome space. In any quotient basis chosen using only $P$, the
remaining matrix therefore has iid uniform entries and $n-r$ rows. Dropping
coordinates is orthogonal projection here because $L$ contains $q$ times
each coordinate axis, so its prefix sublattice spans the full prefix plane.
The two algebraic steps are formalized by
`SigabaNeo.AvgBKZ.coordinateProjection` and
`SigabaNeo.AvgBKZ.quotientColumnCount`. Their Lean statements allow any
surjective residue map and any subspace, respectively.

**Exact profile for this flag (paper).** Put $r_0=0$ and let $r_t$ be the rank
of the first $t$ columns. In the first $t$ coordinates the kernel has index
$q^{r_t}$, by the first isomorphism theorem. The possible last coordinates
of that kernel are exactly $q\mathbb Z$ if the new column is independent of
its predecessors and $\mathbb Z$ otherwise. A basis for the previous kernel
extends by a lift of the positive generator of this subgroup, by subtracting
integer multiples to eliminate the last coordinate. Its new Gram–Schmidt
length is thus $q^{r_t-r_{t-1}}$. Given the prefix rank $r$, the next
log-length equals $\log q$ with probability $1-q^{r-n}$ and zero otherwise.
This is a one-step profile law for a coordinate-adapted basis before BKZ.
Random coordinate permutations preserve the same law.

**A bad suffix can be typical.** For $n\le t<d$, failure of row rank $n$
requires a nonzero left annihilator of the first $t$ columns. Each fixed
projective line of candidate annihilators succeeds with probability $q^{-t}$.
The union bound gives failure at most $(q^n-1)q^{-t}/(q-1)$. Outside this
event the projected lattice equals the entire integer grid. Thus even after
randomly ordering the coordinates the projected lattice can enter the grid
regime with probability near one. Changing its basis by an internal
unimodular transformation preserves every shell count. The thin-shell
counterexamples in [the block geometry note](reverse_minkowski_blocks.md)
apply at their specified dimensions and radii. Independently randomizing
a basis of this suffix cannot enforce a uniform shell-population invariant.

A reduced prefix chosen using the remaining columns does not satisfy the
conditioning argument. A proof for a tour would need a law controlling both
the selected real prefix span and the planted vector relative to it. No
block size or runtime bound for Kyber follows here. The 831.1 and 586.3
bits in [the gap table](../PROOF_GAP.md) are model evaluations with a
heuristic second-minimum input, compared there with 143.8 estimator bits.
Independent adversarial audit of this note is pending.

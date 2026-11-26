---
title: "A shortest-vector prefix changes the metric of the modular quotient"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/avg_bkz2.md` (core v0.1.2).*

# A shortest-vector prefix changes the metric of the modular quotient

Consider one iid uniform row $(u,v)$ over the prime field of order $q$ in
dimension two. Perform exact shortest-vector reduction on the whole plane and
project along the selected shortest vector. With probability at least
$(1-1/q)^2$, the spacing of the resulting one-dimensional Euclidean lattice is
strictly between 1 and $q$. A one-dimensional integer modular kernel at this
modulus has spacing in $\{1,q\}$, for any number of check rows. Thus the total
variation distance between these spacing laws is at least $(1-1/q)^2$.
This holds for every rule for breaking shortest-vector ties.

**Proof.** On $uv\ne0$, write $a=-v/u\bmod q$ using the representative
$1\le a<q$. A basis of the kernel is $(q,0),(a,1)$, of area $q$.
Neither coordinate unit vector belongs to it. The vector $(a,1)$ has length
at most $\sqrt{(q-1)^2+1}<q$. Hence the length $s$ of any shortest vector
satisfies $1<s<q$. It is primitive in the lattice, since a proper integer
divisor in the lattice would be shorter. Its two coefficients in the
displayed basis are coprime, so Bézout completes it to a lattice basis.
The second basis vector projects to a generator of the quotient with length
$h=q/s$, by the base-times-height formula. This proves the claim. The event
has probability $(1-1/q)^2$ by independence. After the prefix is fixed,
rerandomizing a basis of the projected line can change its generator only by
sign.

**Size of the discrepancy.** Put $m=\lfloor\sqrt q\rfloor$. Among the
$(m+1)^2>q$ integer points in $[0,m]^2$ two share a syndrome, so
$s\le\sqrt{2q}$. For any fixed nonzero integer vector of sup norm at most
$R<q$, a uniform row annihilates it with probability $1/q$. For $1\le R<q$,
the union bound gives
$\Pr[s\le R]\le ((2\lfloor R\rfloor+1)^2-1)/q$.
Consequently, with $R=\sqrt q/\log q$, except on an event of probability
$O(1/\log^2 q)$, a nonzero row has
$\sqrt{q/2}\le h<\sqrt q\log q$. The zero row lies in the exceptional event
for sufficiently large $q$. This separates the two metric laws even under
multiplicative distortions smaller than $\sqrt q/\log q$ on the upper endpoint
and $\sqrt{q/2}$ on the lower endpoint.

**Formal coverage.** In namespace `SigabaNeo.AvgBKZ`, `planeShortestSq`
proves the strict squared bounds for every minimizer in the displayed basis.
`planeNormalSq` proves that the squared numerator of the unit-normal
projection is $q^2$ for every unimodular completion. The Euclidean
interpretation, completion, counting and probability bounds above are paper
arguments.

**Scope.** The coordinate projection theorem in [the first note](avg_bkz.md)
uses an orthonormal ambient integer grid. Unimodular coordinates adapted to
the selected prefix can preserve congruences while changing that metric.
In dimension two even the determinant records this change exactly. A model
that conditions on a varying projected ambient metric escapes this
counterexample. Controlling that metric through overlapping blocks in high
dimension, and controlling the joint law with a planted vector, remain open.
The example gives neither a general profile bound nor a provable block size
or cost for Kyber-like shapes.

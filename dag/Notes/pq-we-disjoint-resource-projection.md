---
title: Removing a resource-disjoint path witness before split encryption
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, compilation, cost]
---

Suppose acceptance requires a witness for a public source-to-sink path
selecting p distinct resource labels, and a right witness w passing a
public circuit R(x,w) and selecting q distinct labels Y(w). The only
cross condition is disjointness. Use a layered directed graph with one
label per step and exactly p steps; labels may repeat on the input graph.
The right circuit and selection can be arbitrary polynomial-size circuits.
This shape is part of the input specification. The following compiler
eliminates the whole path witness while preserving each individual right
witness's extendibility.

Use the representative-family exterior-algebra method of
[Fomin, Lokshtanov, Panolan and Saurabh](https://arxiv.org/abs/1304.4626).
Assign distinct field elements a to labels and columns
v(a)=(1,a,...,a^(k-1)) with k=p+q. Choose a public efficiently represented
field with at least the universe size. For example, for an explicit
universe of size N one can find a prime between max(2,N) and twice that
number by sieving. Start with scalar 1 at the source. In layer i, extend
each retained predecessor vector by wedging with the edge's v(a).
At each vertex retain a basis *selected from* these vectors, with path
backpointers. The span equals the span of wedges of all paths to that
vertex: extension is linear, and union of incoming families is span sum.
Repeated labels give zero. Never enumerate source-to-sink paths.

Let the sink basis have rank r <= binomial(k,p). For a right label list Y
wedge its q columns into u. The reduced circuit accepts precisely when R
accepts, the label list is valid, and some stored basis vector wedges with
u to a nonzero scalar. Top-degree wedge is a linear functional; it is
nonzero somewhere on the span exactly when nonzero on a basis vector.
The Vandermonde determinant makes this equivalent to p+q distinct labels.
Thus every accepting reduced witness lifts to an actual compatible path
by following that basis vector's backpointers; any original witness maps
by discarding its path. The circuit can instead store the r selected
p-label lists and use direct equality comparisons with Y. Path identities
are unnecessary in the encrypted predicate.

Let D=max_{0<=i<=p} binomial(k,i). Naive incremental elimination costs
O(|E| (k+1) D^3) field operations as a loose bound, including coordinate
extensions; retained records per vertex are at most D. Right-side
compatibility via label lists uses O(r p q log(2N)) Boolean gates with
binary label identifiers, besides validity and the right verifier.
Encryption compiles this once and invokes the underlying WE for the
reduced verifier. Decryption maps the supplied witness by projection.
A NO instance maps deterministically to a NO instance, so security loss
is precisely the underlying WE advantage bound plus compiler simulation
time, with no new assumption. For split enumeration on b right bits the
balanced item counts become 2^floor(b/2)+2^ceil(b/2), charged at the new
predicate size. The same formula originally included path witness bits.
The field preprocessing and modified per-item predicate cost must both
be charged when comparing actual encryption time.

For p=q=2 the sender retains at most six paths at a sink regardless of
resource alphabet size or number of paths. This cardinality is sharp for
representatives selected from the path family: on a universe of four
labels include all six pairs, and the complement of each pair admits
only that pair. If k=O(log input size), preprocessing and the new predicate
are polynomial; enumeration of an unrestricted right witness can still
be exponential. Shared consistency conditions beyond resource disjointness
require an additional construction. This compiler gives neither a
general CircuitSAT reduction to this special syntax nor a new base WE.

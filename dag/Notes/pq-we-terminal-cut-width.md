---
title: Optimal universal potential width for a batch of connectivity keys
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, composition, cost]
---

Let G be a connected undirected graph with edge predicates as in the
three-terminal masked forest gate. The demand graph H on its terminals
specifies m nonloop output pairs. Edges in H may have multiplicity. Write
c for its maximum cut size counting multiplicity. In a shared forest whose
output keys are functions of endpoint potential differences, the optimal
width for arbitrary terminal partitions is c field words per vertex. The
bound concerns independent uniform hidden output keys in the random-pad
hybrid, a stronger requirement than merely hiding a payload.

**Construction.** Use F of order 2^ell >= m, with an efficient field
representation. Choose d at least c and at most m, and give demand i a
distinct field element a_i and the public vector v_i=(1,a_i,...,a_i^(d-1)).
Handle an empty demand graph by omitting the gate. The sender derives a
d-word pad per G edge from its child seed with a distinct slot. Traverse a
spanning tree to make each tree-edge pad equal its endpoint potential
difference, with the root fixed at zero. On a nontree edge emit its pad
plus its endpoint difference. The i-th output key is the dot product of
v_i and its endpoint difference. A witness path provides the corrected
edge values; sum them, then evaluate one polynomial at a_i.

**Proof.** Fix active edge pads. In the hybrid with independent uniform
inactive edge slots, shifting each active component by an arbitrary vector
and adjusting all edge pads by the induced differences preserves the law
and every correction. Subtracting the root component's shift from all shifts
preserves the differences. The crossing demands are exactly the hidden
outputs. A linear dependency among their changes assigns field scalars h_i
to crossing demands. At each component the sum of its incident h_i v_i
must vanish, by varying its shift; the omitted root equation follows by
summing the others. The incident demands form the cut of that component's
terminal subset, hence number at most c. Their Vandermonde vectors are
independent. Every crossing h_i therefore vanishes. Surjectivity gives
joint uniformity of all hidden keys conditional on the corrections, active
pads and all connected keys, which are fixed by the shifts. The topological
PRG hybrid uses this joint uniformity and exclusive edge slots just as for
three outputs. The reduction adds no new hardness assumption to the
leaf-WE and quantum-secure PRG premises.

**Tight case.** On a realizable partition of all vertices into just two
active components, the active pads determine relative potentials within
each component. After fixing the active pads the crossing endpoint
differences thus depend on a single d-word relative offset. Even nonlinear
public functions of those differences have at most d words of joint
entropy. A cut attaining c requires c independent words. A complete
underlying graph on the terminals with independently available edges
realizes every such cut by enabling edges within each shore. This lower
bound is universal over underlying graphs; restrictions on feasible active
partitions of a given G can improve it.

**Costs and uniformity.** For cycle rank g, correction length is gd ell
bits versus gm ell for independent forests; each child edge supplies d
words rather than m. Encryption takes O(d(|E(G)|+m)) field operations
given the tree and evaluations by Horner's rule. Decoding one path of L
edges costs O(d(L+1)) field operations plus the leaf decryptions and path
discovery. No Max-Cut oracle is needed: any efficiently certified upper
bound on c is safe, including m. For all distinct pairs of t terminals,
m=t(t-1)/2 and d=floor(t^2/4) follows by maximizing s(t-s).
For t=16 this gives 64 words per cycle instead of 120. For bipartite H
the universal width equals m. These are gate costs; the construction
still needs a sound compiler from the original verification relation to
compatible edge predicates and does not bound the size of such a compiler.

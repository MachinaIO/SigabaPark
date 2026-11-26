---
title: Three terminal-pair WE keys from one masked spanning forest
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, composition, cost]
---

Consider three output wires in a monotone WE composition: each opens on
connectivity of a different terminal pair ab, bc, ca in the same undirected
edge-labelled graph. Edge availability must be realized soundly by the
underlying witness predicates. Assume a connected full graph, distinct
terminals, an ell-bit output key, and cycle rank g=|E|-|V|+1.
Running the single-output masked-forest construction three times costs
3g ell public correction bits. The following joint gate uses 2g ell.

Work over binary words. Use one 2ell-bit pad per edge occurrence, derived
from its child seed in a fresh domain. Fix a public spanning tree and root
potential zero. On tree edges set the difference of endpoint potentials
equal to the pad. On each remaining edge publish its pad XOR the potential
difference. An available path now yields its endpoint difference. For each
vertex potential write (U,V) for its two ell-bit halves. For pair ab use
the U difference as output key, for bc the V difference, and for ca the
U XOR V difference. Each available path reconstructs the appropriate key.

**Joint security in the inactive-edge hybrid.** Fix the active edge pads
and external data before this gate; inactive pads in this hybrid are fresh
independent uniform words, including separate slots for repeated labels.
Shift vertex potentials by a constant vector per active connected component,
fixing the root component's shift at zero. Add the resulting endpoint
difference to every edge pad. This bijection preserves all active pads and
public corrections and induces the prescribed potential shifts on the tree.
The output changes are the three projections applied to the terminal
component differences. Connected outputs are fixed. For disconnected
outputs the induced linear map is surjective, as follows:

* With all terminals together there are no hidden outputs.
* With two together the two hidden outputs use two distinct projections
  among U,V,U XOR V on one arbitrary component difference. Any two of these
  projections form an invertible map.
* With three distinct terminal components, their potential shifts can be
  assigned arbitrarily modulo a common translation. A linear relation on the
  three key changes would require the coefficient vectors pulled back by
  the three projections to be equal (collect coefficients at the terminals).
  Their image spaces (x,0), (0,y), (z,z) intersect only at zero.

Thus all hidden keys are jointly uniform conditional on corrections,
active pads and active keys. This allows ordinary independent-seed PRG
hybrids at outgoing wires. In a single gate with no other uses of its
private pads, the public and active data can be sampled while discarding
the corresponding hidden keys. Independent PRG challenges may then
supply their outgoing expansions. This is a local replacement within
the existing topological leaf-WE and PRG proof, assuming nonuniform
postquantum security of those ingredients and classical ciphertexts.

For the same graph and three outputs this saves one third of the public
correction bits and uses 2ell instead of 3ell fresh pad bits per edge.
Tree traversal and path reconstruction use a constant number of word XORs
per visited edge. Leaf ciphertexts, graph description, outgoing expansions
and payloads are additional. For a partial partition with two hidden
outputs, an arbitrary component shift of only ell bits cannot yield two
independent ell-bit translations; this dimension check explains why a
single ell-bit forest with three linear projections fails this proof.
The construction gives an efficient joint gate. A sound general CircuitSAT
encoding into polynomially many such gates and allowed leaf instances
remains open.

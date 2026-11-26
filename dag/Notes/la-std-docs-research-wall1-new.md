---
title: "Simultaneous obstruction for coordinate blocks in the planted embedding"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall1_new.md` (core v0.1.2).*

# Simultaneous obstruction for coordinate blocks in the planted embedding

A low-weight word in the dual of the systematic code is necessary for a coordinate projection to retain even one modular constraint. Counting such words gives a simultaneous obstruction. It allows the coordinate set to be chosen *after* seeing the matrix and the public syndrome, and it applies directly to uniqueness of the shortest pair. No thin-shell estimate is needed.

## Statement and proof

Use the plain-matrix ensemble of [the planted embedding note](usvp_planted.md). Let A be uniform in the m by n matrices over the prime field of order q, fix integer e and s, and put b = As + e modulo q. Let L be the integer kernel modulo q of H = [I_m | A | −b]. The planted vector is p = (e,s,1). For 2 ≤ β ≤ m+n+1 define

$$
D_β=\frac{1}{q-1}\sum_{i=1}^{\min(m,β)}
 {m\choose i}(q-1)^i q^{-n}
 \sum_{j=0}^{\min(n,β-i)}{n\choose j}(q-1)^j .
$$

With probability at least $1-\min(1,D_β)$, **every** projection retaining at most β coordinate axes is the full integer grid on those axes. On this event no coordinate block of dimension between 2 and β has a unique shortest pair, for any projected target.

Indeed a retained set S gives the full grid exactly when the columns outside S span the syndrome space. Sufficiency follows by completing any prescribed residues using those columns and lifting the completion to integers. For necessity, if every retained unit vector lifts then each retained column belongs to the outside span, and H is surjective through its identity block. Dropping coordinates is Euclidean projection along a lattice prefix span since the lattice contains q times every omitted unit vector.

Thus some projection fails to be the grid exactly when some nonzero row vector u has uH supported on at most β coordinates. Its first two parts are u and uA. Discarding the last coordinate only enlarges the event, so its dependence through b costs nothing. For fixed u of weight i, uA is uniform in the field to the power n by column independence and surjectivity. Counting all u by weight, dividing by the q−1 nonzero scalars on each line, and applying the union bound gives the formula. Each grid of dimension k ≥ 2 has k distinct shortest pairs. This argument permits arbitrary tie breaking because the claimed condition itself requires uniqueness.

## Size at the requested shape

For m=n=512 and q=3329 a simpler bound already covers β=400. Indeed the numerator count of pairs (u,uA) of combined weight at most β in the formula is bounded before the probability factor by $2^{m+n}(q-1)^β$, by summing over all supports and allowing the maximum multiplicity on each. Hence

$$
D_{400}\le 2^{1024}(3328)^{399}/3329^{512}
 < 2^{1024}/3329^{113} < 2^{-275}.
$$

The last inequality uses $3329>2^{11.5}$. This is a bound on the probability of even one eligible coordinate projection escaping the grid in the iid matrix model. The value 400 is an obstruction threshold chosen for this calculation. It gives no successful block size or attack cost, and the column independence argument does not cover module Kyber.

## Consequences for the proposed routes

Random orders, progressive coordinate deletion and choosing the best of arbitrarily many coordinate projections all face the same simultaneous event. A single exact solve on such a projected block cannot create uniqueness. A coordinate *section* is different: setting omitted entries to zero retains p only if all its omitted coordinates vanish. For example, if every entry of e and s equals one, no proper coordinate section contains p, whereas all coordinate projections contain its image. This section observation concerns solving for the original plant inside the section.

The [potential argument](wall1_potential.md) requires a guaranteed drop on the defect event. On a grid, internal basis changes preserve the entire set of shortest pairs. Starting from its orthonormal basis, a tour that selects the existing first vector on shortest-vector ties can leave every basis vector fixed. Even in dimension two, the log Gram–Schmidt profile is then (0,0) at every step while uniqueness fails. Randomizing the basis within the fixed projected lattice still preserves that failure. Consequently even a potential tracking the full projected lattice up to isometry cannot force a positive drop for this defect under internal rerandomization. A tour that changes the prefix span can change the projected lattice. The missing estimate there is a joint bound on the competitors and the projected plant for the spans actually reached. The simultaneous support count proved here concerns coordinate spans only.

All results above are paper arguments.

## Independent audit (Nov 2026)

Verdict: **correct**; no wrong step or counterexample. Exact rational arithmetic gives
`D_400 ≈ 2^{−339.3}` (the stated chain gives `2^{−298.2}`, so `2^{−275}` is conservative); the exact
`D_β` stays below 1 up to about `β = 426` (`D_426 ≈ 2^{−20.4}`, `D_428 ≈ 2^{4}`). Implicit points: the
intersection of `L` with the omitted-coordinate span is primitive (full rank in a subspace), hence
extends to a basis; the result is for the iid plain-LWE model with fixed `e, s`, not module Kyber.
Scope: coordinate spans only; general BKZ prefix spans remain open (wall 1 is not solved).

---
title: Removing affine rejection events from a witness verifier by conditional expectations
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, compilation, cost]
---

Let y be the witness bits retained explicitly, z the n private bits and R a
full-row-rank binary matrix. Suppose the verifier accepts exactly when
C(y,Rz) accepts and no event A_j z = b_j(y) holds. Public statement inputs
are implicit. The right sides may be arbitrary public polynomial-size circuits.
The compiler needs an explicit decomposition with this syntax. It may include
all private observations of other gates in R. Put
t_j = rank([R; A_j]) - rank(R).

If the sum of 2^(-t_j) over the proposed block is strictly below one, replace
the verifier by C(y,v) on an unrestricted rank(R)-bit witness component v.
An original witness maps to (y,Rz). Conversely, solve Rz=v and sample a shift
uniformly from ker R. Each event has conditional probability zero or 2^(-t_j),
since its restricted linear map has image dimension t_j. Hence every accepting
reduced witness extends. This argument allows arbitrary overlap among events.

For deterministic extension, choose a kernel basis and fix its coefficients
one at a time. Given a prefix, compute each conditional event probability by
checking consistency and rank on the remaining columns. Take the next bit
with smaller sum of probabilities (break ties arbitrarily). The parent sum
is the average of the two child sums, so it stays strictly below one. At a
leaf it counts violated checks and hence vanishes. These dyadic sums have
common denominator at most 2^n and need O(n+log(2+m)) bits for m events.
There are at most 2nm event-system solves after preprocessing. Encryption
and decryption need no extension algorithm: the sender compiles the public
verifier; the receiver projects the supplied witness. Successive deletions
can be inverted in reverse order if an original witness is needed.

For a specified block this certificate takes polynomial time. Guessing an
optimal block is unnecessary for correctness; exhaustive block search would
invalidate the polynomial compiler bound. For example, take a syntactically
marked block or test the whole list once. An underlying split enumeration
on h bits of y now has h+rank(R) total witness bits. Enumeration of two
balanced parts costs O(2^ceil((h+rank(R))/2)) items, polynomial only when
the retained width is logarithmic in the input size (assuming polynomial
per-item costs). A NO statement maps to a NO statement deterministically,
so any base WE reduction can compose with this map, including against a
quantum distinguisher with a classical statement. The lemma adds no hardness
assumption and supplies no general-NP base WE reduction.

For a tight boundary, let the private bits include three unrestricted bits p
besides protected bits u, and let each event forbid p=b_j(y,u). Seven checks
always disappear, even if all use the identical private coordinates and each
right side depends on the protected witness. With eight distinct constant
right sides every assignment is rejected. The strict inequality cannot be
relaxed on rank information alone.

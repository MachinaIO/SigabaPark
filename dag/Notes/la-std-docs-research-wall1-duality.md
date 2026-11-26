---
title: "What the reversed dual block determines"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall1_duality.md` (core v0.1.2).*

# What the reversed dual block determines

Two integral lattices in dimension three can have the very same reversed dual block, with identical counts of every intrinsic flag, yet give opposite answers to the terminal shortest-line question. In both examples the plant generates the unique ambient shortest line and its projection is primitive.

## Duality for a marked block

Let the first vectors of a basis of a Euclidean lattice L span W. Write P for orthogonal projection onto its complement, Q = P(L), and D = L* ∩ W⊥. In the dual basis, a vector annihilates W exactly when its first coefficients vanish. The remaining dual basis vectors thus span D over the integers. For y in W⊥ the identity ⟨y,Px⟩ = ⟨y,x⟩ gives D = Q*, with duality taken in W⊥. The projected trailing basis vectors form a basis of Q by independence modulo W.

For a plant u in L with Pu nonzero, let a be the positive generator of the subgroup ⟨D,u⟩ of the integers (the image under evaluation). Then Pu/a is primitive in Q. Indeed the evaluations on any basis of D are exactly the coordinates of Pu in its dual basis, and a is their greatest common divisor. This recovers the multiplicity condition of [Part 8](wall1_planted_flags.md).

There is also an exact volume comparison. For every primitive v in Q, its kernel H = D ∩ v⊥ has covolume det(H) = det(D) ‖v‖. Evaluation on v is onto the integers, so a basis of H extends to a basis of D by a vector of evaluation one and height 1/‖v‖. This proves the formula. Conversely each primitive corank-one subgroup of D is the kernel of a surjection onto the integers, unique up to sign, by taking the quotient. The surjection corresponds to a primitive vector of Q. Thus ±Pu are the only shortest vectors precisely when a = 1 and the marked kernel D ∩ u⊥ has strictly smaller covolume than every other primitive hyperplane subgroup of D. Counts without the identity of this marked kernel lose information.

## Identical dual blocks

Take W to be the first coordinate axis. Use the following ordered bases and ambient plants.

| Lattice | First basis vector | Second | Third | Plant |
|---|---|---|---|---|
| A | (12,0,0) | (0,2,0) | (0,0,3) | (0,2,0) |
| B | (12,0,0) | (6,2,0) | (0,0,3) | (0,0,3) |

Both contain 12 times the integer grid. In B, six copies of the second vector minus three copies of the first give (0,12,0). Both project onto the same rectangular lattice of spacings 2 and 3. Consequently their reversed dual blocks even have the same ordered basis, (0,0,1/3) and (0,1/2,0).

In A the ambient shortest pair is the second basis vector and its negative. In B any vector with nonzero second coordinate has the form (12i+6j,2j,3k) with j nonzero. For odd j its first coordinate has absolute value at least 6. For even j its second coordinate has absolute value at least 4. With j zero the unique shortest pair is ±(0,0,3). Both plants retain their full length and are primitive in the common quotient. Its unique shortest pair has length 2. The marked dual kernel therefore has length 1/3 in A and 1/2 in B, although every unmarked flag count agrees.

## Scope for the random model

Kim's Haar mean-value formula provides unmarked flag counts. Dualizing the Haar ensemble preserves its law, since inverse transpose is a group automorphism preserving the integer subgroup and normalized invariant measure. Neither operation identifies which hyperplane is the evaluation kernel of the projected plant. Even the entire unmarked block in the example leaves that identity unresolved. [Kim, *Mean value formulas on sublattices and flags of the random lattice*](https://arxiv.org/abs/2005.10874)

The determinant cutoff in [Part 6](wall1_prefix.md) is also transported exactly. If s is the primitive prefix covolume, block triangular volume gives det(Q) = det(L)/s, hence det(D) = s/det(L). Every failing prefix below the cutoff in [Part 9](wall1_planted_prob.md) therefore supplies a dual block below the corresponding cutoff with the same failure. Reversal alone cannot remove those witnesses from a simultaneous assertion.

The three-dimensional example uses a fixed prefix and composite modulus. It establishes a deterministic obstruction to inference from intrinsic block statistics. The probability that a specified reduction selects a primitive projected plant whose marked kernel strictly minimizes covolume in the prime-modulus planted ensemble remains open. No block size or running time follows here.


## Independent audit (Nov 2026)

Verdict: **correct** (criterion checked in both directions; counterexample verified by enumeration: lattices 12Z×2Z×3Z and
B share the quotient 2Z×3Z and the reversed dual block, marked kernels have covolume 1/3 vs 1/2 with det D = 1/6). Wording:
"identical counts of every intrinsic flag" refers to the shared dual block, not to the ambient lattices (minima 2 and 3).

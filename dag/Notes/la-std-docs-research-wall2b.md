---
title: "Fixed coordinate blocks and dual smoothing"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall2b.md` (core v0.1.2).*

# Fixed coordinate blocks and dual smoothing

Let q be prime and d ≥ 1 the block dimension. Write V_d for the Euclidean unit ball volume and g = V_d^(-1/d) for the determinant-one Gaussian heuristic radius. Normalize the primal block to determinant one before taking its dual D. Put T = 1/λ₁(D). The following probabilities concern a fixed coordinate flag independent of the input.

## Conditional law and short vectors

Write Λ(C) for the integer inverse image of a residue code C. Its dual is q⁻¹Λ(C⊥): pairing with q times the coordinate axes forces denominator q and the remaining integrality conditions are precisely orthogonality to C. Its determinant is q to the codimension of C by counting cosets.

For an iid uniform parity check A, split its columns into a dropped prefix P, a retained block B and a discarded tail. For a coordinate-adapted basis block first restrict the tail coordinates to zero, then project away P. The resulting lattice is Λ(ker H), where H is B reduced modulo the column span of P. If the operation is instead the projection of the *whole* lattice onto B, put all omitted columns into P. Conditional on P the columns of H are iid uniform by the quotient-column count in avg_bkz.md. Conditional also on rank k, row(H) is a uniform k-space in the block by right GL(d,q) invariance. This includes the pre-BKZ coordinate flag and any rank deficiency.

For a lattice generated modulo q by iid uniform generator columns, ordinary projection restricts the generator rows to B. For the flag block with tail set to zero, the coefficient vector must first lie in the kernel of the tail rows. Conditional on those rows, restrict the independent block rows to a basis of that kernel. Each restriction is uniform, independently, so the resulting image code is uniform conditional on dimension. In either construction the residue code of the dual is thus a uniform k-space C conditional on its dimension (for the generator model take the orthogonal complement of the image). In both cases

    D = a Λ(C),     a = q^(-(d-k)/d),     aq = q^(k/d) ≥ 1.

For a nonzero residue the exact inclusion probability is h = (q^k−1)/(q^d−1) ≤ a^d. Indeed each code contains q^k−1 nonzero points, all q^d−1 possible points having equal multiplicity. Equivalently this is the rank-conditioned one-vector Q1 calculation: represent C by the kernel of a uniform full-row-rank (d−k)-by-d check. For a nonzero point, Q1 before conditioning gives q^(-(d−k)); given annihilation, the rows are uniform in its hyperplane. Dividing the full-rank probabilities gives the telescoping factor (1−q^(-k))/(1−q^(-d)) for d−k positive (including k=0); for k=d the inclusion probability is one. Rank conditioning matters since the normalizing determinant depends on it.

For 0 < r < aq the expected number of nonzero points of D in the closed r-ball is exactly h times the number of nonzero integer points of length ≤ r/a. No nonzero multiple of q occurs. In particular

    Pr[λ₁(D) ≤ r | k] ≤ min{(3r)^d, V_d (r + a√d/2)^d}.

For r/a < 1 the count vanishes. Otherwise bounding the integer points by a coordinate box gives (3r/a)^d, and disjoint unit cubes inside the enlarged ball give the second estimate. For failure δ in (0,1), taking r = δ^(1/d)/3 always works, even after mixing over ranks. Thus T < 3δ^(-1/d), within O(√d) of the reciprocal GH scale for δ = exp(−O(d)). When the mesh correction is small and aq exceeds the desired radius, the sharper choice r = g δ^(1/d) − a√d/2 works if positive and strictly below aq. The unavoidable vectors aq e_i explain the cutoff. A saturated coordinate suffix gives the grid, λ₁ = 1, so a constant fraction of g is impossible uniformly in rank.

## Index and cost

Write Lε = √(log(2/ε)/π), 0 < ε < 2. On the first event λ₁ > r, the integer max(1, ceil((Lε/(Rr))^d)) clears Wall 2's necessary pair threshold. Its bit length is O(1 + d max(0,log₂(Lε/(Rr)))). Clearing this threshold alone does not prove smoothing. For example an index-p rectangular sublattice of the grid obtained by multiplying one axis by p has a normalized dual vector of length p^(1/d−1), tending to zero for d > 1.

For the fixed uniform codes one can instead prove smoothing directly. Set θ(s) = Σ_{j∈ℤ} exp(−π s²j²). The exact conditional mean of the nonzero dual mass at width R is

    M = θ(Raq)^d − 1 + h [θ(Ra)^d − θ(Raq)^d].

This follows by summing one-point incidences with positive weights, including the deterministic zero-residue class separately. Hence **p = 1 suffices with failure at most M/ε**, whenever this bound meets the desired confidence. The re-randomization step then costs zero samples and zero lattice operations. For a rank-independent estimate with a ≥ 1/2, the entire lattice lies in a times the grid, giving M ≤ θ(R/2)^d−1. For a < 1/2,

    M ≤ θ(R)^d−1 + (1/2 + 1/R)^d,

using θ(s) ≤ 1+1/s by integral comparison and h ≤ a^d. At R=g ≍ √d both bounds decay exponentially in d: θ(s)−1 ≤ 2 exp(−πs²)/(1−exp(−πs²)). This yields exponential confidence for fixed ε, or for ε decaying more slowly than the stated mass bound. A union bound applies to a predetermined family with the sum of its failure bounds. This cost concerns smoothing only. A grid suffix can satisfy it while failing the shell hypotheses of the sieve.

## Planting and selection

For any coordinate block of any Construction A primal, including the plain-LWE embedding with q times every axis, the projected block lies between qℤ^d and ℤ^d. Therefore its normalized dual minimum is at least 1/q (the normalization multiplies the unnormalized dual by the primal determinant to the power 1/d, at least one). This gives polynomial loss deterministically when q is polynomial in d.

For the full plain-LWE embedding there is also a first-moment bound uniform in the fixed plant e,s. In the notation below take a = q^(−(n+1)/d). A normalized dual vector is a times an integer lift of (u,Aᵀu,−bᵀu). At radius r with r/a < q/2, a nonzero lift must have u nonzero modulo q. Given the first m+n integer coordinates (x,y), the last coordinate is determined modulo q by −eᵀx−sᵀy and admits at most one short lift. For each candidate with x nonzero modulo q the event Aᵀx=y has probability q^(−n). When r/a ≥ 1 the enclosing box therefore gives

    Pr[λ₁(D) ≤ r] ≤ q^(−n) (3r/a)^(d−1) = (3r)^(d−1) q^(m/d).

Below r/a = 1 failure is impossible. With r = min{aq/3, δ^(1/(d−1)) q^(−m/(d(d−1)))/3} failure is at most δ. This calculation uses the dependence of b on A explicitly.

A mesh-independent extension to arbitrary planting is false even with the entire coordinate block and uniform A. In the plain embedding of usvp_planted.md take the fixed admissible secrets e=s=0. Then b=0 and the lattice splits as K × ℤ, where K is the modular kernel of [I_m A] in dimension d−1, d=m+n+1. Its determinant is q^m for every A. Minkowski's ball bound on K* supplies a nonzero vector of length at most 2g_(d−1) q^(−m/(d−1)), with g_j = V_j^(−1/j). Multiply by q^(m/d) to normalize the full dual. Thus T ≥ q^(m/(d(d−1)))/(2g_(d−1)) with probability one. Unrestricted primes defeat any dimension-only polynomial budget. This example conditions on a fixed plant; its frequency under a specified noise distribution is a separate question.

For a reduced prefix, the conditional iid quotient-column step fails: avg_bkz2.md gives a two-dimensional exact-SVP example whose projected spacing lies strictly between 1 and q with probability at least (1−1/q)^2. A one-dimensional modular kernel in the original coordinate metric has only spacings 1 and q. Thus carrying the pre-reduction law through even this first selection is invalid. This does not disprove a different dual tail bound for BKZ. A smoothing index at arbitrary prescribed accuracy for adaptive planted blocks and an end-to-end sieve or attack cost there remain open.

## Formal scope

SigabaNeo.Wall2.incidenceTail proves the finite incidence inequality for an ensemble of constant block size k₀ and constant point multiplicity: the number of blocks hitting B, times the universe size, is at most |B| times the ensemble size times k₀. The inputs here are the nonzero codewords and nonzero residue universe; multiple integer lifts can be merged for this hit bound. The theorem does not assume independence between marks. The uniform-code identification, Gaussian mass calculation, index and planted example above are paper proofs. The targeted Wall2 build reports only propext, Classical.choice and Quot.sound for incidenceTail and dualPair_exceeds.

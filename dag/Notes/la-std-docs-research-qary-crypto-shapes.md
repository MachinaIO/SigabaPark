---
title: "Marked sieve statistics at constant aspect ratio"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/qary_crypto_shapes.md` (core v0.1.2).*

# Marked sieve statistics at constant aspect ratio

Let A have independent uniform entries over the prime field, and put
$s=q^{n/m}$, $L=s^{-1}\\Lambda_q^\\perp(A)$. Fix $0<\\delta<1/2$ and
$\\delta m\\le n\\le(1-\\delta)m$. Write $l=\\lceil\\log m\\rceil$ (natural logarithm).
Take a prime between $\\exp(l^6)$ and twice its ceiling. Then S1, S2 and S3′ of
§3.1 of provable_sieving.md hold simultaneously with probability
$1-\\exp(-\\Omega(m))$. S4 holds with failure $\\exp(-\\Omega(m/l))$.
This includes $m=2n$. The power six is a convenient sufficient choice.

With the algorithmic results and computational model of qary_sieving.md this gives
exact SVP in $(4/3)^{m+o(m)}$ time with high probability, or
$(3/2)^{m/2+o(m)}$ under Hypothesis P. The new argument below uses the
Euclidean nonpartition diagram estimate of g1_audit.md and the shell-volume
estimates of qary_sieving.md. It does not require a rate of Hecke equidistribution.

## The cost of modular coincidences

Use spatial rows, so the integer array has shape $m\\times k$. Suppose its
entries have magnitude at most $sB$, with $B\\ge2$, and the absolute workload
is at most E. Write $t$ for rational rank, $u$ for residue rank. For $u<t$
the entire absolute contribution at the true kernel probability is at most
$$
 E(2sB+1)^{kt}2^k q^{ku}
 [2(t+1)B]^{tm} q^{-(t-u)(m-n)} .
$$
Indeed the rational row space is determined by some ordered list of $t$
bounded integer rows. Choose $t$ pivot coordinates on which projection is
injective on that space. Project the residue span onto these pivots. The
result has dimension at most $u$ and can be specified by $u$ generators
(pad with zeros), at most $q^{tu}$ choices. Its inverse image in
$\\mathbb Z^t$ is a lattice of index at least $q^{t-u}$. A contributing array
supplies $t$ independent points of this lattice in the pivot box.
Their parallelepiped has coordinate displacement at most $tsB$. For their
generated sublattice of determinant $V$, work in each of its cosets in the
inverse image. Disjoint translated parallelepipeds fit in the enlarged box,
so summing over cosets bounds the point count by
$[2(t+1)sB]^t/q^{t-u}$. Projection uniquely determines each rational row.
Raise to the $m$th power and multiply by $q^{-nu}$ (Q1).
This proves the bound, including spaces whose chosen pivot minor disappears
modulo $q$. The rational proxy probability $s^{-tm}$ is smaller on these
arrays. Thus the same bound controls the absolute replacement error even
for signed workloads.

In what follows $k=O(l)$, $\\log B=O(l^2)$ and $\\log\\max(1,E)=O(ml^4)$.
These include shell radii through initialization and powers of grid fibre
means (each normalized grid population is at most $(2B+2)^m$).
The rank replacement costs $\\exp(-\\Omega_\\delta(ml^6))$, summed over ranks.
For fixed $k$, $B\\le m^b$, $E\\le m^{em}$ with fixed $b,e$, the same bound
is $m^{-\\Omega(m)}$ for primes of size $m^{a+o(1)}$ whenever
$a\\delta>bk+e$. This polynomial-modulus statement concerns rank replacement.

## Center on the grid

Use unweighted degrees. Fix the marked grid point $v$ and let $M(v)$ be the
number of grid points in its required two-shell fibre divided by $s^m$.
The grid here is the whole $s^{-1}\\mathbb Z^m$. For targets the two tests
are the terminal or parent shells, translated by $v$; for endpoints they
are the parent and child shell tests defining $a_L$. Uniformly on the mark
band this mean equals the continuum fibre volume times $1+o(1/m)$.
In fact moving a grid point in its cube changes each distance by at most
$\\sqrt m/s$. Widen or narrow both windows by this amount. The
two-distance density and its log derivatives in qary_sieving.md give a
relative error $O(m^{5/2}/(sR))$ on the compact separation intervals used
here. The same sandwich holds for single shells and balls by radial
integration. Throughout a mark band the continuum volume varies by a
factor $1+O(1/m)$ by the same density estimate in the separation.
Denote a representative fibre volume by $M$, and the mark volume by $Q$.
For S2 these centres agree up to $1+O(1/m)$ with the specified degrees
(use pair double counting for endpoints). For S3′ use the bands from
$R^*/2$ through $r_0$ of qary_sieving.md.

Expand the marked $2h$th moment about $M(v)$, with $h=l$ for S2 and $h=1$
for S3′. Replace the modular probabilities by rational probabilities using
the preceding bound. The following details explain how the grid preserves
the exponential accuracy required after centering.

* For a partition diagram in the enumeration of g1_audit.md the free
  columns are the mark and one occurrence per block. Later occurrences
  equal their parent or, for targets, its reflection $v-x$. Both choices
  preserve the exact grid fibre. Temporarily remove the rational independence
  requirement on the free columns. For $t$ free columns of rank $d<t$,
  enumerate their rational row space by $d$ bounded rows and project onto
  $d$ injective coordinates. There are at most
  $(2sB+1)^{td}(2sB+1)^{dm}$ arrays, each charged the *original* $s^{-tm}$.
  Even after workload factors, binomial coefficients and all
  $\\exp(O(k\\log k))$ partition choices this costs
  $\\exp(-\\Omega_\\delta(ml^6))$. In particular overlaps introduced by
  unrestricted reconstruction are harmless.
* At a fixed mark, unrestricted partition contributions factor over
  blocks. A singleton has exactly the mass $M(v)$, cancelling the choice
  of a deterministic centre with opposite sign. More explicitly, after
  fixing all blocks of size at least two, each remaining labelled slot
  sums over these two choices independently. Each block of size $j$ has
  mass at most $2^{j-1}M(v)$. At most $h$ blocks survive. Thus the
  partition moment is bounded by
  $Q\\exp(O(h\\log(2h)))M^h$ when $M\\ge1$; here the normalized outer grid
  sum and the variation of $M(v)^{2h}$ cost $1+O(h/m)$.
* For all other diagrams use an upper bound on each unsigned raw term.
  Choose maximum-minor pivots as in qary_sieving.md and write $D$ for
  the index of the admissible pivot lattice, $T$ for reconstruction.
  Put $H=\\lceil\\exp(l^5)\\rceil$. In a dyadic index bin $[d,2d)$ there
  are at most $2^k(2d)(4d+1)^{k^2}$ spaces (entries of $T$ lie in
  $D^{-1}\\mathbb Z$ and have magnitude at most one). For $D>H$ use the
  parallelepiped argument above with index $D$, retaining the spanning
  restriction. Per space the rationally weighted absolute sum is at most
  $E[2(t+1)B]^{tm}D^{-m}$. The bin series costs
  $\\exp(-\\Omega(ml^5))$ in total.
* For $D\\le H$ drop spanning, split the pivot lattice modulo $D$, and
  put a cube of side $D/s$ at each pivot sample in each residue class.
  The normalized sum of shell indicators is bounded above by the
  corresponding integral with every distance window extended at both
  ends by $2k\\sqrt m H/s$, multiplied by $D^{-m}$. Indeed each cube
  stays inside the extended tests by the entry bound on $T$; there are
  $D^{(t-1)m}$ product residue classes. Bound centre factors separately by
  $[M(1+O(1/m))]^{2h-j}$ for $j$ retained occurrences. No signed
  quadrature is used. Changing to the ordered marked pivots in the
  integral gives exactly the coefficient of g1_audit.md by its lattice
  index Jacobian (qary_sieving.md). Now sum the enlarged integrals over
  the nonpartition spaces, including additional indices for an upper bound.
  This step keeps the same rational spaces classified as partitions before
  and after enlargement.

For clarity, the estimates from the continuum audit apply with this
enlargement: its relative size is $o(m^{-A})$ for every fixed $A$.
The free pivot masses and outer volume change by $1+o(1/m)$ by the
two-distance and radial sandwiches. The longitudinal residual is still
$O(k/m^2)$, smaller than $1/l^2$ at the endpoint $\\gamma=(l-1)/l$;
for targets its integral parity test is unchanged. Transverse lengths
still have relative error $O(m^{-2})$. Consequently the same Gram
determinant bounds, denominator weights and height-bin sums in that audit
give for the absolute nonpartition terms together
$$
 Q M^{2h-1}\\exp(O(k^2\\log m))
 \\left[(16/27+o(1))^{m/2}+(e/4+o(1))^{m/2}+2^{-m}\right].
$$
Indeed a nonpartition term with $j$ occurrences has at most $j-1$ free
occurrence pivots; the remaining centre factors supply $2h-j$ powers.
All factors from the moment expansion are absorbed in the prefactor.
This uses only the unweighted version of the audit (drop the weights in
its pivot integrals). The enlargement avoids requiring exponentially
small relative errors on the individual partition integrals.

Divide by $(cM)^{2h}$ for a fixed constant $c>0$ small enough that
every S2 violation exceeds this deviation. The factor $c^{-2h}$ is
subexponential. At the smallest step the partition ratio $Q/M^h$ has
logarithm per dimension at most $\\tfrac12\\log(4/3)-1/3+o(1)$ by the
volume calculation in §3.10. The correction has $Q/M\\le
(4/3)^{m/2}e^{o(m)}$, and each of the three resulting bases is strictly
below one. Increasing radius scales $M,Q$ by the same factor. Summing
over the two mark types and $O(l^3)$ steps proves S2. For S3′ remove
the inner ball by Q1 and Markov (physical radius below $q$), costing
$2^{-m+o(m)}$. In the remaining $O(m^2)$ bands, $Q=e^{O(m/l)}$ or
smaller and $M\\ge(13/12)^{m/2}e^{-O(m/l)}$. An uncovered mark contributes
$M(v)^2$. The partition and correction bounds divided by this threshold
are exponentially small, as required.

## Ordinary counts, filter work and scope

For one shell or ball let $N$ count its nonzero lattice points. Its mean
is its normalized grid count by Q1 (physical radius below $q$), hence
$(1+o(1))$ times its volume for the sieve shells and S4 ball. In the
second moment the rationally independent pairs at proxy probability
$s^{-2m}$ cost at most $(\\mathbb EN)^2$. On each rational line through
a given nonzero point there are at most $2sB+1$ points in the box,
by projection to a nonzero integer coordinate. These pairs cost at most
$(2sB+1)\\mathbb EN$. The modular error above is negligible.
Since $sB=e^{O(l^6)}$, Chebyshev gives S1 with exponentially small
failure and S4 with failure $e^{-\\Omega(m/l)}$. Rank failure costs at
most $q^{n-m}$. On full rank the dual residue space is uniform, and
rounding in the dual mesh $s/q$ gives the same dual minimum estimate
as in qary_sieving.md since $q/s\\ge q^\\delta$. This supplies S5 there.

For the product-filter work bound the same rational-line estimate costs
at most $(2sB+1)(1+o(1))V_R C_m$ since the joint probability is at most
one cap probability $C_m$. The independent-pair proxy costs at most
$(1+o(1))V_R V_{R'} C_m^2$: condition on the filter axis, count both
shell caps by exterior cubes, then integrate. The angular threshold $1/2$
moves by $O(\\sqrt m/(sR))$; integrating the density proportional to
$(1-t^2)^{(m-3)/2}$ shows relative cap error $o(1)$ (a subinterval of
length $1/m$ above threshold lower bounds its tail by a constant times
the threshold density divided by $m$). The rank error is negligible.
This gives the two Lemma H work terms up to $e^{o(m)}$, sufficient in
the forward, reverse and terminal work estimates since $sB=e^{o(m)}$.
The success and time conclusions use the same algorithmic and Markov
steps as §3 of provable_sieving.md.

At fixed order and polynomial radii the modular estimate already allows
polynomial primes at ratio two. The complete shrinking-tree theorem here
uses a quasi-polynomial prime, including for the large initialization
shell. A fixed prime such as 3329 is outside both estimates. In fact
$q e_i/s$ has bounded length at fixed prime and ratio two, whereas
$R^*/2$ grows like $\\sqrt m$; the inner-ball removal in this proof then
fails deterministically. Finite Kyber dimensions, module structure,
planted short vectors and the conditional distribution of projected BKZ
blocks need separate analysis. No LWE attack cost follows.

The geometric counts, grid cancellation and probability estimates are
paper proofs. Lean formalizes the finite one-sided transfer inequality
as `SigabaNeo.QAry.meanValue_le_add_defect` in `QAry/RankDefect.lean`.

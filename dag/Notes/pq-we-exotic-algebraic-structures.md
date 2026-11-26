---
title: WE beyond lattices, part 2 - invariant maps, higher-dimensional isogenies, equivalence problems, rank metric, non-abelian and tropical algebra (verdicts)
refs: [definition:WE_CircuitSAT, note:pq-we-non-lattice-algebras, note:pq-we-rank-gap-lattice-barriers, note:pq-we-gap-structure-routes, theorem:AdvancedEncryption.WE.RankGap.card_solutions_le, theorem:AdvancedEncryption.WE.Codes.exists_affine_relation, theorem:AdvancedEncryption.WE.Codes.card_le_of_sparse_preimages, theorem:AdvancedEncryption.WE.Syzygy.exists_affine_syzygy]
tags: [witness-encryption, barrier, dead-end, strategy]
---
Design-AI sub-task on `Def_WE_CircuitSAT` (NAND Circuit-SAT, 128-bit witnesses, `2^12` gates,
128-bit concrete security): look for a **post-quantum** algebraic structure that gives the
"linear tests only" behaviour used by the rank-gap witness encryption of Hair–Sahai (arXiv
2609.18275, §3) and by Jutla's anti-concentration variant (ePrint 2026/2995), or some other
restricted partial homomorphism, from a falsifiable, statement-independent assumption. It
continues `pq-we-non-lattice-algebras` (regular group actions, LPN and codes, Goldreich's PRG, MQ)
and does not repeat it. Three precise lemmas were proved in this pull request as theorem nodes
with complete proofs: `AdvancedEncryption.WE.Exotic.canonical_linear_test_hsp`,
`AdvancedEncryption.WE.Exotic.rank_equiv_combination` and
`AdvancedEncryption.WE.Exotic.rank_support_mono`. The rest is informal.

## 0. The interface that would have to be realized, and a quantum obstruction to it

Hair–Sahai's encryption publishes handles `X_i = [s_i]`, `Y_j = [sᵀ M_j r]` in a **fresh group of
prime order `p ≈ 2^m`**, and decryption computes `Z = Σ a_j Y_j` and `H = Σ u_i X_i` with
**arbitrary known coefficients in `F_p`** ("multiplication of a handle by a known scalar costs
`O(log p)` group queries", §3.1), then tests `Z ∈ {H, 2H, …, m²H}`. Jutla keeps the same mechanism
(the coefficients come from linear forms evaluated at powers of a public seed, also arbitrary in
`F_p`). The coefficients `a_j` are the coordinates of the witness matrix `A(b)` in a computed basis
of the space `S` (HS §5.1), so they are not small.

**Lemma (canonical labels make a hidden-subgroup instance;
`AdvancedEncryption.WE.Exotic.canonical_linear_test_hsp`).** If hidden values `z` of a commutative
ring have a canonical label `F(z)` (any injective map) and anyone can compute the label of
`x + y·s` from known `x, y` and a published encoding of a hidden `s`, then
`(x, y) ↦ F(x + y s)` is constant exactly on the cosets of `L_s = {(a, b) : a + b s = 0}`, and
`L_s` determines `s`.

Over `Z_p` this is the abelian hidden-subgroup problem on `Z_p²`, solved by Shor's algorithm with
polynomially many superposition queries to the label map. Consequence: **any instantiation of the
HS / Jutla
interface in which (i) equal hidden values get equal labels and (ii) multiplication by an arbitrary
known scalar is efficient is quantumly broken**, whatever assumption backs it. This is a sharper
form of "generic groups are not post-quantum": it is the *interface the decryptor needs* that is
broken, not a particular group. A post-quantum structure with a linear-test decryption must
therefore give up one of the two:

* **(i) canonical labels** — encodings are randomized or noisy, and equality is a predicate, not a
  label (lattices, codes). Then the test is a noisy or approximate zero test, and the barriers of
  `pq-we-rank-gap-lattice-barriers` (Barrier 1: linear-only is a knowledge assumption) and the
  exact fake zeros of `AdvancedEncryption.WE.Codes.exists_affine_relation` apply.
* **(ii) efficient scalar multiplication** — only small coefficients are available (group actions,
  invariant maps, §1). Then honest decryption needs a rank-gap reduction whose witness
  coefficients `(a, u, c)` are small integers. No such reduction is known: the HS and Jutla
  coefficients are full-size elements of `F_p`.

(Whether a quantum algorithm needs labels at all, or can work from an equality predicate on
randomized encodings, is not settled here; the lemma only covers the labelled case.)

## 1. Isogenies

### 1a. Cryptographic invariant maps (Boneh–Glass–Krashen–Lauter–Sharif–Silverberg–Tibouchi–Zhandry, arXiv 1807.03038)

This is the one proposal whose interface matches §0 option (ii) exactly. For ordinary curves with
CM by `O` and the class group `Cl(O)` acting freely and transitively, the products
`(a_1 ⋆ E) × ⋯ × (a_n ⋆ E)` and `(a_1⋯a_n) ⋆ E × E^{n−1}` are isomorphic as unpolarized abelian
varieties (their eq. (2)). A computable isomorphism invariant `isom` would give
`e_n(E_1, …, E_n) = isom(E_1 × ⋯ × E_n)`, an equality test on **sums of hidden class-group
exponents** with nonnegative integer coefficients of total size `n` (and signs via quadratic
twists). This is precisely the "parallelization" that a plain group action lacks
(`pq-we-non-lattice-algebras` §1): in exponent notation the adversary and the decryptor can test
`Σ c_i ℓ_i = Σ c'_i ℓ_i + g` for small `c, c'`.

* **Status: no candidate.** The paper states the invariant as an open problem; theta nulls, Igusa
  invariants and Kummer-surface invariants depend on a choice of polarization and are not
  invariants of the unpolarized variety (their §5); the Deligne invariant is equivalent to solving
  the isogeny problem (their Thm 5.1). For supersingular curves over `F_{p²}` all such products are
  isomorphic for `n ≥ 2` (Deligne, their Remark 4.4), so the map is trivial there. An explicit
  isomorphism `E_a × E_b → E_{ab} × E` is a `2 × 2` matrix of isogenies and reveals isogenies
  `E_a → E`, so only a *non-constructive* invariant could work. A web search (Nov 2026) found no
  later progress or attack on this open problem.
* **Even with the invariant:** it breaks isogeny-DDH (their Remark 4.2), so security can only
  rest on computational invariant-map assumptions or on an idealized model. Rank-gap security is
  a statement about *all* linear tests, i.e. the idealized-model argument again (Barrier 1 of
  `pq-we-rank-gap-lattice-barriers`); no falsifiable assumption is known that limits the adversary
  to linear tests here either.
* **Large coefficients restore Shor.** The decryptor needs coefficients in `[0, h)` (`h = #Cl(O)`).
  The standard fix, publishing encodings of `2^k ℓ_i` for all `k ≤ log h`, makes the map
  `y ↦ isom(⋯)` of `y·ℓ_i` computable for every `y` in polynomial time; `isom` is canonical, so
  the lemma of §0 applies and Shor recovers `ℓ_i`. Without such encodings, only polynomially large
  coefficients exist, and quantum attacks fall back to hidden-shift (Kuperberg-type,
  subexponential) algorithms, which also force large parameters.
* Encryption itself would be implementable: exponents `sᵀ M_j r` can be formed as integers and
  applied as ideal classes (reduced forms) with an effective action for arbitrary ideals
  (Clapoti, KLaPoTi, PEGASIS use 2- and 4-dimensional isogenies for this). That is not the
  obstacle.

**Verdict: best structural match, but conditional on an open problem in arithmetic geometry, on
a small-coefficient rank-gap reduction that does not exist, and on an idealized-model proof. Not
usable for `Def_WE_CircuitSAT`.**

### 1b. Higher-dimensional isogenies (Kani's lemma; SQIsign2D-style tools)

What they add: evaluating isogenies of arbitrary (non-smooth) degree from interpolation data
(SQIsign2D-West/East, PRISM), effective class-group actions for arbitrary ideals (PEGASIS), and
new trapdoors (FESTA / QFESTA / POKE-type PKE). What they do to an adversary: Kani's lemma
**recovers** a hidden isogeny of known degree from images of enough torsion points (Castryck–Decru,
Maino–Martindale–Panny–Pope–Wesolowski, Robert, Eurocrypt 2023). Torsion images are the natural
"partial homomorphism" of isogenies (the isogeny acts on `E[N] ≅ (Z/N)²` as a `2 × 2` matrix), and
higher-dimensional isogenies turn exactly this leakage into a full break; masked variants
(M-SIDH) survive only by hiding the degree and with large parameters. Pairings compatible with
isogenies (`e_N(φP, φQ) = e_N(P, Q)^{deg φ}`) live on smooth-order torsion or in `F_{p^k}^*`, where
discrete logarithms fall to Shor. **Verdict: dead.** Higher-dimensional isogenies enlarge the set
of tests available to the adversary; they supply no hard bilinear or linear-only structure. Their
only use here is efficiency of a group action (and of a hypothetical invariant map).

### 1c. Class-group actions with twists

Covered by `pq-we-non-lattice-algebras` §1 (two-term relations, twists only give the sign). With
an invariant map it becomes §1a.

## 2. Equivalence problems: LIP, code equivalence, matrix code equivalence, tensor / ATFE

Lattice isomorphism (Ducas–van Woerden, Eurocrypt 2022; HAWK), linear and permutation code
equivalence (LESS), matrix code equivalence (MEDS) and alternating trilinear form equivalence
(ALTEQ; tensor-isomorphism-complete, Ji–Qiao–Song–Yun TCC 2019, Grochow–Qiao) are all of one
shape: a group `G` (`GL_n`, monomial, orthogonal, `GL_m × GL_n`, `GL_n` acting on three modes)
acts **linearly** on a space `V`, and an encoding is `g · v` for a hidden `g`.

* Operations: linear combinations of encodings that share one `g` are computed in the clear,
  `Σ c_j (g · v_j) = g · (Σ c_j v_j)`; there is no product, and encodings under different `g`
  cannot be combined at all. The structures are non-commutative, so no key agreement or
  parallelization exists (PKE from LIP uses a decoding trapdoor of a remarkable lattice, not a
  homomorphism).
* Tests: every `G`-invariant of the combination. For the problems to be meaningful the action must
  preserve the relevant metric (rank for MCE and tensor slices, Hamming weight for code
  equivalence, the quadratic form for LIP), and these are the metrics a rank-, weight- or
  norm-gap decryption would test.

**Lemma (`AdvancedEncryption.WE.Exotic.rank_equiv_combination`).** For invertible `A, B` and any
coefficients, `rank(Σ a_j A M_j B) = rank(Σ a_j M_j)`.

So a MinRank space published under a hidden equivalence is the statement's own MinRank instance:
the honest decryptor's rank-one combination and every adversarial low-rank search have the same
answer as on the public `M_j`. **Correctness forces the decryption metric to be `G`-invariant, and
then the secret `g` plays no role in security**; the remaining hardness is MinRank (or minimum
distance, or SVP) of the statement itself, a statement-dependent problem that
`pq-we-gap-structure-routes` already examines (and that is in the clear on YES instances). If the
metric is *not* `G`-invariant, the honest test fails on `g · A(b)`. Equivalence problems also have
no analogue of the hidden scalars `s, r` that carry the message in HS. **Verdict: dead** for
rank-gap WE; they remain useful for signatures (Fiat–Shamir over group actions).

## 3. Noisy polynomial systems, rank metric, non-commutative and tropical algebra

* **Noisy polynomial systems / LWR or LWE over polynomial rings / noisy MQ.** A degree-`d` noisy
  system in `n` variables is a noisy *linear* system in the `C(n + d, d)` monomials (Veronese
  linearization) with a structured secret. Any public test is then covered by the affine relation
  lemma (`exists_affine_relation`, over fields) or the degree-`d` form of the affine-syzygy
  argument (`exists_affine_syzygy`, over the integers), with the dimension replaced by the monomial
  count, still polynomial for constant `d`. Ring and module versions of LWE / LWR, including
  non-commutative ones (matrix rings, cyclic algebras, group rings), are lattice problems and fall
  under `pq-we-rank-gap-lattice-barriers`. Noisy polynomial reconstruction (Naor–Pinkas) is broken
  by list decoding and lattice reduction (Bleichenbacher–Nguyen). **Verdict: no new structure.**
* **Rank metric (rank syndrome decoding, RSL; ROLLO / RQC).** Here the Hamming obstruction of
  `pq-we-non-lattice-algebras` §2 disappears. **Lemma
  (`AdvancedEncryption.WE.Exotic.rank_support_mono`).** For `K / F` and any matrix `H` over `F`,
  the support of `e H` lies in the support of `e`, so the rank weight does not grow. With the
  coordinate gadget of `K` over `F` (preimages are `F`-coordinate expansions) every `F`-linear
  evaluation, including BGG+-style evaluation with `F`-valued inputs, has **zero** noise growth,
  in contrast with `card_le_of_sparse_preimages`. But this cuts both ways: since no `F`-linear
  combination changes the noise support, noise never gates anything; decryption is gated only by
  exact `F`-linear cancellation of the secret part, which anyone finds by Gaussian elimination
  (`exists_affine_relation` gives exact fake zeros for `N ≥ d + 2` encodings). All evaluated
  samples also share one error support, which is the Rank Support Learning setting; RSL with many
  samples has polynomial attacks (Debris-Alazard–Tillich, Asiacrypt 2018, broke the rank-metric
  IBE of Gaborit–Hauteville–Phan–Tillich this way). Rank-metric preimage trapdoors (RankSign) are
  broken too. Barrier 3 of `pq-we-rank-gap-lattice-barriers` (evaluation needs the input, i.e.
  the witness, at encryption time) applies unchanged. **Verdict: dead**, but the lemma corrects a
  possible reading of the Hamming lemma: the absence of an LPN gadget is a Hamming-metric fact, not
  a code-based one.
* **Tropical (min-plus) algebra.** Addition is idempotent, so there is no cancellation and no
  hiding of a linear combination; tropical key exchanges (Grigoriev–Shpilrain) are broken
  (Kotov–Ushakov 2018), and tropical linear systems are solved by mean-payoff-game algorithms.
  **Verdict: dead.**

## 4. Hard non-abelian groups

Shor-type attacks need an abelian hidden subgroup; non-abelian groups avoid them only if they have
no efficient faithful low-dimensional linear representation. Every concrete proposal so far has
one or an equivalent weakness: matrix groups `GL_n(F_q)` reduce discrete logarithms to extension
fields via eigenvalues (Menezes–Wu 1997), hence to Shor; braid groups have the faithful
Lawrence–Krammer representation, giving polynomial-time linear-algebra attacks on braid
Diffie–Hellman (Cheon–Jun, CRYPTO 2003), besides length-based attacks; polycyclic and other
platform groups fall to similar algebraic or heuristic attacks. The non-abelian hidden-subgroup
problems that resist quantum algorithms (symmetric and general linear groups) are exactly the
**equivalence problems of §2**, whose action is linear on the encoded object. For rank-gap WE a
non-abelian group offers no addition at all; adding a linear representation to get one puts the
linear structure in the clear (§2). **Verdict: dead.**

## 5. Combinatorial designs composed with LPN noise

Subspace designs and rank condensers (HS §5.2, and Jutla's single list of forms at powers of a
seed) are public, deterministic linear maps used **inside the NP-hardness reduction** to make the
rank gap; they preserve low rank of every small column space. They carry no secret, so composing
them with LPN noise yields noisy-linear encodings of the same `sᵀ M_j r` and inherits Barrier 4 of
`pq-we-rank-gap-lattice-barriers` and the fake zeros of `exists_affine_relation`. Moreover a rank
condenser helps the adversary: it compresses the MinRank search to a smaller space without losing
low-rank elements. In the rank metric the noise does not grow (§3), so it cannot gate either.
**Verdict: dead.**

## Summary

| Structure | Operations available | Adversary's tests | Falsifiable "linear-only"? | Verdict |
| --- | --- | --- | --- | --- |
| Invariant map (isogeny, open) | sums of hidden class-group exponents, small coefficients | equality of small-coefficient sums; with powers of 2, Shor | no (idealized model); invariant unknown | conditional lead, not usable |
| Higher-dimensional isogenies | arbitrary-degree evaluation, effective actions | recover isogenies from torsion images; smooth pairings | no | dead |
| LIP, code / matrix code equivalence, ATFE | linear combinations in the clear under one hidden `g` | all `G`-invariants (rank, weight, norm) | security does not depend on `g` | dead |
| Noisy polynomial systems, non-commutative LWE | linearization | linear tests on monomials | no | no new structure |
| Rank metric (RSD, RSL) | free `F`-linear evaluation (no noise growth) | exact Gaussian elimination, RSL attacks | no | dead |
| Tropical algebra | min-plus combinations | tropical linear algebra | no | dead |
| Non-abelian groups | group law | linear representations, length attacks | no | dead |
| Designs / condensers + LPN | public linear maps | as LPN; condensers help search | no | dead |

**What remains.** Lemma §0 says that a post-quantum version of the HS interface must drop either
canonical labels or efficient scalar multiplication. Dropping labels leads back to noisy encodings
(lattices), where the open question is the one of `pq-we-rank-gap-lattice-barriers`. Dropping
scalar multiplication leads to small-coefficient interfaces (group actions, invariant maps), where
the precise open question is combinatorial and assumption-free: **is there an NP-hard rank-gap (or
anti-concentration) reduction from Circuit-SAT whose YES witness gives a low-rank element of the
space with coefficients `a_j, u_i, c` that are small integers (in a fixed public basis), while the
NO side keeps the gap over `Z_h`?** Even a positive answer would only give a construction over an
invariant map that does not exist, with an idealized-model proof; it is recorded as the only
structural lead found, not as a route to `Def_WE_CircuitSAT` under the task's constraints.

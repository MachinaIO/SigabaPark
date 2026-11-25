---
title: WE beyond lattices - LPN and codes, isogeny group actions, Goldreich's PRG, MQ and their combinations with LWE (verdicts)
refs: [definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.Codes.card_fresh_le_finrank, note:pq-we-hybrid-count-barrier, note:pq-we-rank-gap-lattice-barriers, note:pq-we-evaluation-oracle-crux, theorem:AdvancedEncryption.WE.Syzygy.exists_affine_syzygy, theorem:AdvancedEncryption.WE.Codes.card_le_of_sparse_preimages, theorem:AdvancedEncryption.WE.Codes.exists_affine_relation]
tags: [witness-encryption, barrier, dead-end, strategy]
---
Design-AI sub-task on `Def_WE_CircuitSAT` with **non-lattice** post-quantum assumptions and their
combinations with each other and with LWE: LPN (binary, large field, ring, low-noise, dual / syndrome
decoding, learning subspace with noise), code-based assumptions, isogeny group actions (CSIDH-type),
Goldreich's local PRG and sparse-LPN (NC0) assumptions, and multivariate-quadratic (MQ) assumptions.
The constraints are those of `pq-we-route-survey`: falsifiable, statement-independent, no route
through iO, no evasive LWE. The barrier of `pq-we-hybrid-count-barrier` is algebra-independent and
is taken as given: a proof needs about `2^128` witness-indexed hops. The arguments are informal
except the three counting lemmas, which are theorem nodes with complete proofs. Part of the analysis
was cross-checked with a second AI model; every claim below was checked by the submitting agent.

## 1. Isogeny group actions: commutativity, but no gating

**Scope.** Abelian, free and transitive ("regular") actions as in CSIDH / CSI-FiSh. Two other
families are outside this model: *linear* actions on vector spaces (code equivalence, matrix code
equivalence, alternating trilinear forms), where linear combinations are computed in the clear and
the hidden object is the group element, so a rank-gap analogue (matrix rank is invariant) is a
statement-dependent problem in the clear (Barrier 3 of `pq-we-rank-gap-lattice-barriers`); and
higher-dimensional isogeny tools (Kani's lemma, torsion-point images, Weil pairings), whose
pairings live on smooth-order torsion groups where discrete logarithms are easy, so they give no
hard bilinear map.

**Model.** An abelian group `G` acts freely and transitively on `X` (CSIDH: the class group on
supersingular curves over `F_p`). Published set elements `x_i = ℓ_i ⋆ x_0` have hidden `ℓ_i`. A
generic algorithm (generic group action model: Montgomery–Zhandry, Asiacrypt 2022; Duman et al.,
PKC 2023, ePrint 2023/186) can apply group elements it knows in the clear, take quadratic twists
(`(g ⋆ x_0)^t = g^{-1} ⋆ x_0`) and test equality.

**Observation.** Every set element such an algorithm produces has the form `(g ± ℓ_i) ⋆ x_0`
(additive notation in the exponent) with `g ∈ G` known in the clear, and every equality test is a
**two-term** relation `±ℓ_i ∓ ℓ_j = g − g'`. Combining two hidden elements into
`(ℓ_i + ℓ_j) ⋆ x_0` is the parallelization (group-action CDH) problem, assumed hard; that is what
makes the action a cryptographic assumption.

**Consequences.**

* A decryptor's key `K = KDF(κ ⋆ x_0)` is reachable only as `(g ± ℓ_i) ⋆ x_0`, so with a valid
  witness the decryptor must compute **in the clear**, from public data and `w`, one of the `2N`
  fixed offsets `g = κ ∓ ℓ_i`. All gating by `φ(w)` happens in that clear computation. In
  group-action ElGamal the offset is the secret key; in WE there is no secret key, so the scheme
  is "WE whose hidden secret is one of `2N` group elements", followed by a commutative key
  derivation. Commutativity gives key agreement (and WE for group-action-DDH-type languages), but
  it does not help gate a general circuit `φ`.
* Hair–Sahai's decryption test `Σ a_j Y_j = c · Σ u_i X_i` needs sums of hidden elements, i.e.
  parallelization. The honest decryptor cannot run it, so **rank-gap WE is not even correct** over
  group actions. The same holds for Jutla's variant (ePrint 2026/2995) and for any test with three
  or more hidden terms.
* Gentry–Lewko–Waters positional WE needs degree-`n` products along the witness; a group action has
  no product at all. A "positional component" held in a group action can only be moved by known
  shifts `g`, which the adversary can also apply, so it cannot hold a hidden position.
* **Group action + LWE.** By the first point the group-action part reduces to a KDF on a value
  that the LWE part must already compute, so the combination is no stronger than the LWE part
  alone. Twists add only the sign `±`.
* Group-action discrete logarithms fall to Kuperberg-type hidden-shift algorithms in
  sub-exponential quantum time, so parameters must be sized against them (Peikert, Eurocrypt 2020,
  and Bonnetain–Schrottenloher, Eurocrypt 2020, estimate CSIDH-512 below its claimed quantum
  level). This only affects cost, not the verdict.

**Verdict: dead** for gating NAND-circuit SAT, alone or combined. What regular group actions do
give (PKE, OT, weak PRFs and Naor–Reingold-type PRFs, signatures, WE for their own DDH-type
languages) is all available from LWE already.

## 2. LPN and codes: no gadget, hence no statement-independent evaluation

**Lemma (sparse preimages are expensive; `AdvancedEncryption.WE.Codes.card_le_of_sparse_preimages`).**
For any finite alphabet `F` and any map `f : F^N → T`, if every `t ∈ T` has a preimage with at
most `ρ` nonzero entries, then `|T| ≤ ((N + 1) |F|)^ρ`. For a linear map onto `F^n`:
`ρ ≥ n log|F| / log((N + 1)|F|)`.

**Why it matters.** BGG+ evaluation (the only known statement-independent way to put the
statement into public matrices, `pq-we-rank-gap-lattice-barriers` Barrier 3) multiplies encodings
`sᵀA + e` by a short preimage `G^{-1}(X)` of an arbitrary target. In the Hamming metric of LPN and
codes, "short" means sparse, and the lemma says that any public matrix with sparse preimages of
every target needs column weight `ρ ≥ n / log₂(2N + 2)` (binary case), and by the same count all but a
`2^{−n/2}` fraction of targets need weight `≥ n / (2 log₂(2N + 2))`, so random targets (as in
BGG+) are expensive, not only the worst one. Over `F_2`, an output bit of
`e · h` with `wt(h) = ρ` and `e ← Ber(τ)^N` has bias `(1 − 2τ)^ρ` (piling-up lemma). Correct
decryption with bias `β` therefore needs `τ ρ ≲ ln(1/β)/2`, i.e.
`τ ≲ log₂(2N+2) · ln(1/β) / (2n)`. Plain Gaussian elimination on `n` samples (all noise-free with
probability `(1 − τ)^n ≈ e^{−τ n}`) then costs about `β^{−log₂(2N+2)/2} · n³`. A decryptor needs
`≈ 1/β²` repetitions to see the bias, so an attacker spending the honest decryption work raised
to the power `log₂(2N+2)/4` breaks LPN after **one** level of gadget evaluation, and better
attacks (BKW, ISD) only lower this. Lattices escape because their noise is additive in a norm
with a super-polynomial ceiling `q`; in the Hamming metric the ceiling is a noise rate of `1/2`
(`1 − 1/p` over `F_p`, where the lemma is even worse). This is the quantitative reason why
there is no LPN-based FHE, ABE for circuits, or **public** BGG+ analogue (a map of public matrices
`A ↦ A_φ` with sparse preimages). Known LPN homomorphism is bounded-degree and private or
interactive: sparse LPN gives multi-party homomorphic secret sharing for bounded-degree polynomials
(Dao–Ishai–Jain–Lin, CRYPTO 2023, ePrint 2023/1593), and sparse LPN plus a linearly homomorphic
encryption gives somewhat homomorphic encryption for `o(log λ)` multiplications
(Corrigan-Gibbs–Henzinger–Kalai–Vaikuntanathan, Eurocrypt 2025, ePrint 2024/1760). These use
sub-constant noise rates and evaluate on secret-keyed ciphertexts, which is not the public
statement-into-matrix evaluation that BGG+ provides.

**Consequence: the public code must carry trapdoor-derived, statement-dependent data.** Write an
LPN-type ciphertext as `CT = sᵀA + e + m·u` with decryption `⟨CT, h_{φ,w}⟩` (any F-linear
decryption has this form; `A` is everything public that multiplies the secret). The vector
`h_{φ,w}` is computed in the clear from public data and `w`. Since `s` is uniform, correctness
needs `A h_{φ,w} = 0`, and the noise needs `h_{φ,w}` sparse. Take the constant-true circuit `φ_1`:
the decryption procedure, run on any `w`, outputs a sparse dual codeword of `A`.

* If the encryptor builds `A = A_0 L_φ` from a uniform (or fixed-law) `A_0` and a public,
  trapdoor-free `L_φ` (the shape a statement-independent reduction would simulate from LPN samples
  `sᵀA_0 + e_0`), then `L_{φ_1} h` is a sparse-enough dual vector of `A_0` (the noise `⟨e_0, L h⟩`
  must stay biased), so the decryptor for `φ_1` is an efficient LPN distinguisher. Contradiction.
* So `A` (or hints published with it) must be produced with a trapdoor and depend on `φ`. For a
  false `φ`, a statement-independent proof must simulate those hints without the trapdoor. In
  lattices this is done by a gadget trapdoor (`SampleRight` from the `−G` structure, as in the
  leaf lemma of `pq-we-tree-candidate-crux`), i.e. by sparse/short preimages of arbitrary targets.
  The lemma above says the Hamming metric has no such gadget at usable noise rates.
* Otherwise NO-case security is a decoding assumption on a statement-dependent code (the Hamming
  analogue of Barrier 3 of `pq-we-rank-gap-lattice-barriers`), or statistical, which
  `pq-we-hybrid-count-barrier` excludes for NP-complete languages.

This is not an impossibility proof (a non-gadget trapdoor simulation for codes is not excluded),
but it removes the only known mechanism.

**Rank-gap over LPN encodings** (Direction 3 of `pq-we-route-survey`; Barrier 4 of
`pq-we-rank-gap-lattice-barriers`). Hair–Sahai need a **public** zero test. If it is a public
F-linear map `T` from encodings to `F^d` followed by a Hamming-weight threshold, then by
`AdvancedEncryption.WE.Codes.exists_affine_relation` any `N ≥ d + 2` encodings have a nonzero
combination `λ` with `Σ λ_j = 0` and `Σ λ_j T(enc_j) = 0` **exactly**, and Gaussian elimination finds
it in polynomial time. Such fake zeros pass every weight threshold. They do not by themselves
distinguish encryptions (they exist for every message and statement), but they show that the zero
test is **unsound**: the generic-group abstraction that Hair–Sahai's proof uses (only true
equalities pass) fails, so the proof cannot be transported. A sound version must restrict to
*sparse* combinations (support well below `1/τ`), i.e. the security claim becomes "no sparse
combination of the decryption form can be found": a decoding problem on the code spanned by the
encodings, whose structure comes from the statement's matrices `M_j`. That is a
statement-dependent assumption, unless a statement-independent proof with about `2^128`
witness-indexed hops is supplied (`pq-we-hybrid-count-barrier`); the rank-gap proof is not of that
form. The linear-only restriction of Barrier 1 is not supplied by LPN: an adversary may run ISD,
which is non-linear.

**Verdict: dead** for LPN, large-field LPN, ring-LPN, dual LPN / syndrome decoding and learning
subspace with noise, alone. All are linear with Hamming noise, and the lemma applies to each.

### 2b. LPN's constant noise escapes the affine-syzygy argument only in a narrow sense

The affine short-syzygy argument against data-only witness-indexed hybrids
(`AdvancedEncryption.WE.Syzygy.exists_affine_syzygy` is its counting step) writes one decryption
vector `h_r` as an affine combination of later live ones and needs the summed error to stay below
the decoding gap. Over a field the combination comes from linear algebra with no coefficient bound
(`exists_affine_relation`; and by `AdvancedEncryption.WE.Codes.card_fresh_le_finrank`, among `K`
vectors at most `dim` indices `r` have `h_r` outside the span of the later ones, so a random planted
position is good with probability `≥ 1 − dim/K`). The last step is where Hamming noise differs:
if each live decryption bit is only correct with probability `1 − τ_dec`, an `F_2`-combination of
`t` live decryptions is guaranteed correct only when `t τ_dec < 1/2` or so (and when the hybrid
moves `m_0 → m_1` rather than `m → uniform`, when `(t + 1) τ_dec < 1`).

Three qualifications (the first two found in the cross-check with the second model, then checked):

* **Linear noise model.** If the hybrid ciphertext is itself "linear structure plus one noise
  vector `e`", the live decryption errors are `⟨e, h_t⟩`, and an exact relation
  `h_r = Σ β_t h_t` gives `⟨e, h_r⟩ = Σ β_t ⟨e, h_t⟩` with no error growth: `Z_r` is then a single
  honest-looking noisy decryption, and the barrier's contradiction is back. The escape needs hybrids
  whose errors on different witnesses are not of this form.
* **Short relations.** The escape needs the vectors `h_w` to have no relation with few terms.
  Selection-type decryption (`h_w = Σ_i E_{i,w_i}`) has 4-term rectangle relations; a map
  `w ↦ h_w` of `F_2`-degree `d_w` has `(2^{d_w+1} − 1)`-term subcube relations; and a truly *random* map
  is incompatible with succinct correctness (by a union bound over the `2^N` ciphertexts, one
  ciphertext cannot be within decoding distance on `2^{127}` independent random functionals unless
  `N` is exponential). So `w ↦ h_w` must be highly structured and of high degree at once.
* **Linear reductions.** Suppose a hop is proven by a reduction that embeds an LPN (or LWE)
  challenge `b` linearly, `CT = L b + C` with `(PK, C, L)` independent of `b`. For every witness
  `t` that stays live in both hybrids, `Lᵀ h_t ≠ 0` would make the live decryption `⟨CT, h_t⟩`
  uniform in the uniform branch, so `Lᵀ h_t = 0` except with small probability. (This assumes each functional is
  needed; with majority over many functionals the reduction may randomize a minority of them, which
  this argument does not cover.) Then `Lᵀ h = 0`
  on the whole span of the live functionals, and by `card_fresh_le_finrank` this span contains
  `h_r` for all but `dim` planted positions `r`: such hops cannot change the decryption functional
  at those positions *at all*, whatever the noise rate. Turning this into a full barrier needs a
  statement of where those positions must die; that step is open, but it shows that the noise escape
  can only be used by a reduction that embeds its challenge non-linearly.

Two further obstacles remain for any LPN design using the escape: `h_{φ,w}` must satisfy
`A h_{φ,w} = 0` for witnesses only (Section 2: planted, statement-dependent structure), and in an
LPN + LWE combination the LWE layer has bounded noise, so the barrier applies to it, and data must
pass from the LWE layer to the LPN layer through a non-linear step (the "non-linear processing"
escape, not the noise escape).

A concrete design was attempted in the cross-check (Gap-NCP encoding of the statement plus
prefix-hashed positional LPN vectors `u(w), v(w*)` with `⟨u(w), v(w*)⟩ ≈ [w < w*]`, majority over
2048 blocks). It is broken several ways: the circuit-derived parity-check matrix has many
constant-weight dual vectors (local gate redundancies), so belief-propagation decoding recovers the
secrets of the statement part; Prange ISD on the statement part runs in time `2^{O(γ)}` for gap
`γ` of the known Gap-NCP reductions (only constant gap is NP-hard under deterministic polynomial
reductions); and its intended hop to LPN on the statement-independent positional matrix fails by the
linear-reduction point above.

## 3. Goldreich's PRG and sparse-LPN (NC0) assumptions

* As **decryption-side non-linearity**, a locality-`D` predicate applied to ciphertext bits is a
  multilinear integer polynomial of degree `D` (coefficients at most `2^D`), so it is covered by the
  degree-`D` form of the affine-syzygy argument (dimension `N^D · d_out`, still polynomial for
  constant `D`). Followed by a majority vote it falls under the noise escape of Section 2b, with the
  same qualifications. Only super-constant depth escapes otherwise, and then the decryption is an
  arbitrary circuit.
* As an **assumption**, Goldreich's PRG (and MQ, below) gives one-way functions and PRGs; sparse
  noisy equations (Applebaum–Barak–Wigderson, STOC 2010) give PKE. Their structural gift is constant degree with polynomial
  stretch, used to expand randomness inside bounded-degree homomorphic schemes (in key generation
  or encryption, not in decryption). Sparse-LPN homomorphism is bounded-degree and private
  (Section 2), so no public statement evaluation results.
* In **combinations** (Goldreich + LWE), the PRG enters as the seed expansion inside a homomorphic
  evaluation, as in the tree candidate (`pq-we-tree-candidate-crux`); its crux (the internal step
  is 2-key FE) does not depend on which PRG is used. Using Goldreich's PRG is a cost optimization
  (NC0 evaluation inside BGG+), not an escape.

**Verdict:** useful as a cheap PRG inside lattice constructions; no escape.

## 4. Multivariate-quadratic assumptions

The MQ problem (solve a random system of quadratic equations over `F_q`) is a falsifiable,
statement-independent search assumption. It gives one-way functions, PRGs (QUAD) and signatures
(UOV, MAYO, MQDSS), but no PKE: every trapdoor MQ encryption scheme relies on hidden structure
beyond plain MQ. WE for NP plus a one-way function gives PKE (Garg–Gentry–Sahai–Waters, STOC 2013),
so WE from MQ alone would give PKE from plain MQ, a long-open problem. In combinations MQ offers a degree-2
PRG and the bilinear polar form `Q(x+y) − Q(x) − Q(y) + Q(0)` (used for MQ identification
schemes), but neither supplies a zero test or a public statement evaluation. **Verdict: no
structural contribution to gating.**

## Summary

| Algebra / combination | What it gives | Why it does not gate `φ(w)` statement-independently |
| --- | --- | --- |
| Regular group actions (CSIDH) | PKE, OT, (weak) PRFs, key agreement | only two-term relations; gating happens in a clear computation of an offset |
| Group action + LWE | — | the GA part only derives a key from what the LWE part computes |
| Linear actions, higher-dimensional isogenies | — | combinations in the clear (statement-dependent) / pairings with easy DLOG |
| LPN, F_p-LPN, ring-LPN, dual LPN, LSN, codes | PKE, OT, linear homomorphism | no gadget (sparse-preimage lemma); public linear zero tests have fake zeros (affine relation lemma); a correct scheme needs a statement-dependent code |
| LPN constant noise | escapes the last step of the affine-syzygy argument | not for linear noise models or linear reductions; needs structured high-degree `w ↦ h_w` and a planted code; the one concrete attempt is broken |
| Goldreich PRG / sparse LPN | PRG, PKE (ABW10), private bounded-degree HE/HSS | constant locality is constant degree: covered |
| MQ | OWF, PRG, signatures | no PKE; PRG / polar-form role only |

All these algebras are **weaker** than LWE for WE purposes, because the one tool every
statement-independent WE attempt uses (statement-independent evaluation of `φ` into public
matrices, BGG+) is lattice-specific, and the sparse-preimage lemma explains why. The remaining
open problem stays lattice-internal: the second representation of `w ↦ sᵀ A_{U_w}`
(`pq-we-evaluation-oracle-crux`). Non-lattice assumptions can at most contribute PRGs, key
derivation, or a Hamming-noise output layer to it.

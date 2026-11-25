---
title: NP-hard gap structures as the carrier of WE security - why the NO-side structure cannot replace the hybrid walk, problem by problem
refs: [definition:WE, definition:WE_CircuitSAT, note:pq-we-hybrid-count-barrier, note:pq-we-rank-gap-lattice-barriers, note:pq-we-matrix-collision-barrier, theorem:AdvancedEncryption.WE.Hybrid.stat_hops_carry]
tags: [witness-encryption, barrier, strategy, dead-end]
---
Design-AI sub-task: use NP-hard problems that are not yet common in cryptography, and let the
structure that a **NO** instance must have (the soundness side of an NP-hardness-of-approximation
result, such as Hair–Sahai's "every nonzero matrix of `S` has rank `≥ R`") carry the security of
WE for `Def_WE_CircuitSAT`, together with a falsifiable statement-independent assumption (LWE and
its variants, LPN, isogenies, Goldreich's PRG). This note records what that idea can and cannot
do. The arguments are informal complexity arguments; the one counting step is the Lean theorem
`AdvancedEncryption.WE.Hybrid.stat_hops_carry` (proved). Parts were cross-checked with a second
AI model; every claim kept here was checked by the submitting agent.

## 1. A gap problem does not change the language

An NP-hardness reduction `φ ↦ x_φ` (Circuit-SAT to a gap problem `Π`) is efficient and maps true
statements to YES instances and false ones to NO instances. So a WE scheme for `Π` *with a given
security proof* is a WE scheme for Circuit-SAT with the same proof: the encryptor runs the
reduction first. Every barrier stated for Circuit-SAT (`pq-we-hybrid-count-barrier`) applies
verbatim. The choice of `Π` can only matter through **how the proof uses** the NO-side structure.
There are three ways to use it, examined in §2–§4.

## 2. NO-side structure inside a reduction: simulation-type reductions flatten

`pq-we-hybrid-count-barrier` covers hops that are statistical on NO instances or computational
under an assumption that "holds for every `φ`". A natural hope is a computational hop whose
*reduction* needs the NO structure (for instance, it embeds an LWE challenge in a way that is
only correct because every matrix of `S` has high rank, or because `λ₁(L_φ)` is large). Then the
hop need not be indistinguishable on YES instances, and the barrier as stated does not apply.

**It still applies to every simulation-type reduction.** Call a reduction for the hop
`H_i → H_{i+1}` simulation-type if it is an efficient sampler `R(φ, z)` such that, for every NO
instance `φ`, `R(φ, z ← X_0)` is statistically close to `H_i(φ)` and `R(φ, z ← X_1)` to
`H_{i+1}(φ)`, where `X_0 ≈ X_1` is the statement-independent assumption (`X_0`, `X_1`
efficiently samplable, as for LWE and LPN). Replace the hop by three:

1. `H_i → R(φ, X_0)`: statistical on NO instances;
2. `R(φ, X_0) → R(φ, X_1)`: computational for **every** `φ`, YES instances included, because
   `R` is efficient (any distinguisher composed with `R` attacks the assumption);
3. `R(φ, X_1) → H_{i+1}`: statistical on NO instances.

All new hybrids are efficiently samplable. (Intermediate hybrids that are not efficiently
samplable, or are defined only on NO instances, do no harm: the triangle inequality merges the
statistical hops between consecutive computational hops into one statistical hop between
samplable endpoints.) On a YES instance the decryptor has advantage `≈ 1`
between the ends, has negligible advantage on every hop of type 2, so the statistical hops carry
almost all of it (`stat_hops_carry`: total `≥ 1 − δ − |C| ε`), while on NO instances each of
them is negligible. A random statistical hop is then a Statistical Difference instance with gap
`1/T` versus negligible, so `L ∈ SZK`. Applied recursively, a proof tree built from
simulation-type reductions and statistical steps flattens in the same way (as long as the
flattened tree has polynomially many leaves).

Two refinements (the first suggested by the second model, checked here):

* **Statement-dependent polynomial-size advice does not escape either.** If the reductions `R_m`
  are polynomial-size circuits that depend on `φ` arbitrarily (even uncomputably), Merlin can send
  them and Arthur runs the AM protocol for the complement of Statistical Difference on the
  flattened chain. On a YES instance no polynomial-size `R_m` lets the decryptor distinguish
  `R_m(φ, X_0)` from `R_m(φ, X_1)` (non-uniform hardness of the assumption), so the statistical
  hops must carry the advantage and Merlin cannot cheat. This puts `L ∈ coAM`.
* **The argument needs non-uniform hardness** of the statement-independent assumption, because
  the decryptor hard-wires `(φ, w)`. This is standard for LWE / LPN, and Sigaba's cost model
  (description length counts) is of this kind.

Consequences for the three sub-ideas of this task:

* **NO-side property that is not efficiently checkable** (the gap side is coNP-hard to verify):
  irrelevant. The SZK argument never checks the property; it only uses statistical closeness on
  NO instances and the decryptor on YES instances.
* **"Usable computationally but not statistically"**: if the use is a simulation-type
  reduction, it flattens as above. Otherwise the indistinguishability on NO instances is a
  statement-dependent assumption (e.g. "Gaussian cosets of `L_φ^*` are pseudorandom whenever
  `λ₁(L_φ) ≥ γ d`"), which is excluded.
* **Average case from worst case on the NO side** (map a worst-case NO instance to a random-looking
  object, then use an average-case assumption): this is a simulation-type reduction, so it
  flattens too.

**What escapes the flattening** (each is a requirement on a surviving design):

* (a) super-polynomially many hops (witness-indexed hybrids, the route of
  `pq-we-hybrid-count-barrier`);
* (b) hybrids that are not efficiently samplable, e.g. defined from `2^n`-time computations on
  `φ` or on the ciphertext randomness. In the concrete setting a reduction may spend `2^128` time
  if the premises are raised accordingly. But the only thing exhaustive search over witnesses
  learns about `φ` is `φ ≡ 0`, which the proof already knows; the open question is whether it
  can compute something useful about the *ciphertext* (e.g. a representation of a pseudorandom
  function from its truth table without the key), and no example is known;
* (c) **non-simulation reductions**: the reduction runs the adversary on inputs outside the
  honest ciphertext distributions (malformed ciphertexts, rewinding, search-to-decision) and its
  success analysis uses `φ ∉ L`. A Gentry–Wichs-style meta-reduction against such reductions
  (replace a random NO statement "`y ∈ Im(PRG)`" by a pseudorandom YES statement and the
  inefficient adversary by the decryptor) does not go through directly, because the
  maximum-likelihood adversary and the decryptor may answer malformed queries differently. The
  closest precedent is the computational soundness of interactive *arguments* for NP
  (Brassard–Chaum–Crépeau; Kilian's PCP + collision-resistant hashing): the reduction rewinds the
  cheating prover to extract a collision, and its success uses that no witness exists. WE is
  equivalent to special-honest-verifier zero-knowledge arguments with logarithmic prover
  communication (Liu–Mazor–Pass, as cited by Hair–Sahai §1.3), so escape (c) is the question of
  proving soundness of such a *laconic* argument by a rewinding reduction to LWE. We know no WE
  proof of this kind;
* (d) idealized adversaries (generic groups, linear-only encodings): excluded here.

## 3. The number of hops the SZK argument actually forces

The argument turns a proof with `T` hops into an SZK protocol whose cost is polynomial in `T`, so
it excludes `T = poly` under `NP ⊄ coAM`. It does **not** by itself force `T ≈ 2^n` (`n = 128`
witness bits). To exclude `T = 2^{εn}` it needs the hypothesis that UNSAT on `n` variables has no
`2^{O(εn)}`-time AM protocol, an "AM-ETH"-type hypothesis. The strong form (time `2^{(1-o(1))n}`)
is already false for some classes: Williams (CCC 2016, arXiv 1601.04743) gives MA proofs running
in `c^n` time with `c < 2` for #Circuit-SAT of sublinear-depth circuits. Instantiating the
Statistical-Difference-to-AM step (polarization, then Goldreich–Vadhan) costs roughly `T^2` to
`T^4` times the sampler cost; with LWE-size samplers at `n = 128` this is not in conflict with the
`2^{n/2} = 2^64`-time MA protocols unless `T` is below about `2^16`–`2^32` (rough estimate from the second model;
the exponents depend on the protocol used). So the witness-indexed
`2^128`-hop accounting of `pq-we-hybrid-count-barrier` (premises of about `128 + 2·128` bits) is
what a design over *all* witnesses costs, not a lower bound. A proof whose hops are indexed by a
part of the witness, each hop using a coNP fact about all completions (verified by the reduction
in `2^{n−t}` time, escape (b)), is not excluded by the SZK argument either. It would still face
the function-hiding problem of the witness-indexed designs.

## 4. The gap problems one by one

**A unifying reduction.** In every scheme whose decryption is one short integer combination
`c(w)` of LWE/LPN samples on public matrices (BGG+-free, one linear step), and `c(w)` lies in an affine lattice
`V_φ = {c : cᵀ A_φ = t (mod q)}` determined by the public data. Any short vector of `V_φ`
decrypts, whether or not it comes from a witness. So, whatever the source problem (rank, distance,
labels), a noisy-linear scheme is secure on `φ` only if `V_φ` has no short vector: the source gap
matters only through the **induced lattice gap** on `V_φ`, and the lattice row below applies.
Two concrete forms of this attack: the linear closure of `pq-we-matrix-collision-barrier`
(MinRank), and the *linear-relaxation attack* for constraint problems: if decryption cancels
secrets edge by edge along a labeling, any small-denominator solution of the affine (LP)
relaxation of the labeling problem cancels them too, and the uniform fractional labeling is such
a solution. Since linear relaxations are solvable in polynomial time, NP-hard problems always have
NO instances whose relaxation is feasible (integrality gaps).

The natural encoding for each problem is noisy-linear (LWE/LPN samples whose short dual
combination is supplied by the witness). For each, the NP-hard regime and the regime where the
NO side gives *statistical* security are disjoint, as §2 predicts, and the regime in between needs
a statement-dependent assumption.

| Problem | NP-hard gap (source) | NO-side structure used | Verdict |
| --- | --- | --- | --- |
| Homogeneous MinRank | `1` (rank-one `u vᵀ`, `v ∈ {0,1}^m`) vs `(log m)^c`, randomized poly-time; deterministic for a supplied prime `p ≥ 2^m` (Hair–Sahai arXiv 2609.18275, Thm 1.2 and Thm 6.1); constant gaps earlier (Guruswami–Ren–Tang) | every nonzero matrix of `S` has rank `≥ R` | dead: noisy-linear encodings are closed under short linear combinations and `{0,1}` rank-one matrices span everything, so rank cannot gate access (`pq-we-matrix-collision-barrier`); the GGM proof is a linear-only argument (`pq-we-rank-gap-lattice-barriers`, Barrier 1) |
| Minimum distance of codes (Hamming) | every constant factor: Dumer–Micciancio–Sudan (randomized), Cheng–Wan (deterministic, fixed fields), Austrin–Khot, Micciancio; superconstant only under quasi-polynomial reductions; the superlogarithmic gap needed by Barta–Ishai–Ostrovsky–Wu is open (as recalled by Hair–Sahai §1.3–1.4) | all nonzero dual codewords have weight `≥ d_N` | dead. LPN encoding `y = G s + e`, `e ← Ber(η)^N`: a weight-`d_Y` dual codeword decrypts only if `(1 − 2η)^{d_Y} ≥ 1/poly`, i.e. `d_Y = O(log N / η)`; by the XOR lemma `y` is statistically uniform once `d_N` is a constant fraction of `N − k` (for constant `η`). Ratio `Ω(N / log N)`: far outside the NP-hard range, and inside SZK by §2 |
| GapSVP (ℓ₂) | every constant (Khot 2005; Haviv–Regev 2007, randomized poly-time); `2^{(log n)^{1−ε}}` under randomized quasi-polynomial reductions (Haviv–Regev); deterministic for ℓ_p, `p > 2` (Hair–Sahai, cited as [HS26]) | `λ₁(L_φ) ≥ γ d` | dead. Encoding `t = e mod L_φ^*`, `e ← D_σ`; a vector `v ∈ L_φ` of norm `d` decrypts if `d σ ≤ 1/ω(√log n)`; the coset is statistically uniform once `σ ≥ √n / λ₁(L_φ)` (Banaszczyk). So statistical security needs `γ ≳ √n · polylog`, where GapSVP is in coAM ∩ SZK (Goldreich–Goldwasser: `√(n / log n)`) and in coNP (Aharonov–Regev: `√n`). The NP-hard range `γ ≤ n^{o(1)}` needs "`e mod L_φ^*` is pseudorandom for this `φ`": statement-dependent |
| Label cover / PCP CSPs | `1` vs `δ` (PCP theorem, projection games with small soundness: Moshkovitz–Raz) | every *global* assignment violates a `1 − δ` fraction | dead: per-constraint locks are opened by *local* assignments, and the adversary may choose them inconsistently across constraints (mixing). Enforcing global consistency is the multilinear-map step of GGSW-style exact-cover WE |
| Polynomial systems (Nullstellensatz / SoS degree) | refutations of degree `≥ D` (proof-complexity lower bounds; used inside Hair–Sahai's moment-matrix reduction) | a degree-`D` pseudo-expectation exists | dead: a pseudo-expectation only fools *linear* tests of degree `≤ D` on the encoded moments; noisy-linear encodings allow non-linear tests, so this is Barrier 1 again (linear-only) |
| Tensor rank | exact tensor rank is NP-hard (Håstad 1990) | high rank of every element of a tensor space | dead for the same reason as MinRank (it is MinRank with one more mode) |
| Subset sum / knapsack | exact | no subset hits the target | dead: low-density instances fall to lattice reduction; the affine-determinant-program candidates are broken on false subset-sum instances (Jo, cited by Hair–Sahai §1.3) |
| Isogeny paths, group actions, permutation groups | no NP-hardness known to us for the cryptographic variants; group-action and isomorphism-type problems tend to lie in coAM-like classes | — | not a source of an NP-hard gap; usable only as the statement-independent assumption |

Code gaps transfer to MinRank by the diagonal embedding (`rank diag(v)` is the Hamming weight
of `v`): homogeneous MinRank inherits the constant-factor hardness of minimum distance, and
affine MinRank that of nearest codeword. The YES matrices are then diagonal, not rank one, so
these instances do not support Hair–Sahai's short-search decryption.

**Two candidates built during this task, both dead.**

1. *Rank gap as an LWE-dimension gap.* Publish `y_j = P M_j s + e_j` for a basis `M_j` of the
   MinRank space and let the decryptor combine `Σ a_j y_j = P (u vᵀ) s + Σ a_j e_j`, a rank-one
   (hence low-dimensional, LLL-solvable) LWE instance, while on NO instances every combination is
   LWE of dimension `≥ R`. Dead: the coefficients `a_j` of Hair–Sahai's reduction are arbitrary
   elements of `F_p` with `p ≈ 2^m`, so `Σ a_j e_j` is not small; with small coefficients the
   linear-closure attack applies; and a polylogarithmic rank gap gives at most a quasi-polynomial
   LWE gap. No witness-indexed hybrid exists either, since every `y(w)` shares `s` and `P`.
2. *Label cover with LWE cancellation.* For each edge `e = (u, v)` and label `a`, publish
   `c_{e,a} = ⟨a_e, s_{u,a}⟩ + ⟨b_e, t_{v,π_e(a)}⟩ + m_e + noise`, with `Σ_{e∋u} a_e = 0`,
   `Σ_{e∋v} b_e = 0` and additive shares `m_e` of the message; a satisfying labeling `σ` sums
   `c_{e,σ(u)}` and all secrets cancel. Dead by the linear-relaxation attack: summing *all*
   `c_{e,a}` (the uniform fractional labeling, for regular projections) also cancels every secret
   and yields `|Σ_U| · m⌊q/2⌋ + noise`, which reveals `m` when `|Σ_U|` is odd (otherwise other small-denominator points of the relaxation are used).

## 5. Gap structure inside a witness-indexed walk

In a `2^n`-hop walk (escape (a)), a gap reduction offers a *robust* local fact: a wrong candidate
violates a `1 − δ` fraction of PCP constraints, or gives a matrix far from `S`. Robustness does
not help with the obstacles recorded for witness-indexed designs: those concern the keys or the
decryption shape (function hiding, the evaluation oracle), not the strength of the local fact.
The only use found for robustness is threshold secret sharing over constraints per candidate,
which dies by the mixing attack of the label-cover row.

## Verdict and the lead that remains

Using an NP-hard gap problem changes nothing by itself: the NO-side structure helps exactly when
it gives statistical security, and then the language is in SZK. Every route through a
simulation-type reduction, a non-checkable property, or a worst-to-average-case step on the NO side
flattens into that case (§2). The remaining open escapes are (a) witness-indexed walks (where
function hiding is the obstacle), (b) hybrids that need exponential time to sample, and (c)
non-simulation reductions that query the adversary outside the honest ciphertext distribution and
use `φ ∉ L` in their analysis. Escape (c) is the one no recorded barrier covers; a precise first
question is whether a Gentry–Wichs-type meta-reduction rules out black-box reductions from WE for
NP to a falsifiable statement-independent assumption when the reduction may make malformed
queries.

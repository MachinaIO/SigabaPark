---
title: Praxis (Tse-Vanjani-Vesely) without pairings - what it needs from the bilinear generic group, post-quantum substitutes, and why its decryption functionality alone admits a quantum key recovery
refs: [definition:WE_CircuitSAT, note:pq-we-rank-gap-lattice-barriers, note:pq-we-hybrid-count-barrier, note:pq-we-affine-syzygy-barrier, note:pq-we-linear-hop-barrier, note:pq-we-non-lattice-algebras, note:pq-we-multipass-ggh15, note:we-circuitsat-bruteforce-explicit-cost, theorem:AdvancedEncryption.WE.RankGap.card_solutions_le]
tags: [witness-encryption, barrier, strategy, dead-end]
---
Design-AI sub-task (y) on `Def_WE_CircuitSAT`. Source: *Praxis: Practical Witness Encryption for
NP* (Tse, Vanjani, Vesely; ePrint 2026/2971 = arXiv 2611.28552), read in full from the paper's text
(Sections 2-6 and Appendix B). Praxis follows Hair-Sahai's rank template (arXiv 2609.18275, §3).
Its hidden table `y rᵀ` is factored by a QAP into two width-2 factors that a pairing multiplies.
It ties weighted copies so that every *easily guessed* cheat has rank at least 4, using Module-SIS
and an inverse Littlewood-Offord theorem mod `q`. It is proved extractable in the bilinear generic
group model (GGM) plus the random-oracle model.

The question here: can a post-quantum object replace the pairing group, with a falsifiable,
statement-independent assumption replacing the GGM step?

Summary:

* **No, for Praxis as specified.** Praxis's own decryption needs (i) `F_q`-linear combinations in
  two source groups, (ii) one pairing, and (iii) *canonical names* of target elements, used by the
  key oracle `H_key([κ]_T)` and by the baby-step giant-step search. Any encoding that provides
  these, noisy or not, lattice-based or not, gives a polynomial-time **quantum** attacker a
  hidden-subgroup oracle on two published quotient powers. That oracle reveals the QAP point `τ`,
  and from `τ` the key element is a public `F_q`-multiple of one pairing (§3). The attack needs no
  witness and no hardness break. So no choice of encoding or assumption helps. Every known degree-2
  lattice encoding has a noisy *linear* zero test, and such a test yields canonical names for free
  (§3.3).
* **The GGM step cannot become a falsifiable, statement-independent assumption with a polynomial
  reduction.** What the GGM supplies is the "algebraic adversary" restriction plus a statistical
  count. Any per-instance replacement has an admissibility condition. On false statements that
  condition is itself computational (MSIS), and deciding it contains SAT (Lean lemma
  `rankOne_passing_iff_witness`, below). So the replacement is evasive-shaped, statement-dependent
  or knowledge-type. The hybrid-count barrier blocks the remaining route (§4).
* **What survives is classical:** Praxis applied directly to the `Def_WE_CircuitSAT` circuit
  (`N ≈ 4224` Boolean unknowns) costs about `2^{30}` bits of ciphertext and about `2^{53}` bit
  operations to decrypt, against `2^{97}` for MP2/MP3 and `2^{188}` for the brute-force baseline.
  But its premises are a pairing group and the GGM, outside the problem's registry and broken by
  Shor. For this `N`, MSIS can even be dropped: take at least `N + 1` forms (§5).

Lean (complete proofs, Mathlib only, in this PR):
`AdvancedEncryption.WE.Praxis.rankOne_passing_iff_witness`,
`AdvancedEncryption.WE.Praxis.zeroTest_search_card_le`, and
`AdvancedEncryption.WE.Praxis.period_iff_and_ratio`. The rest is informal, and every step was
checked by the submitting agent against the paper's text.

## 1. What Praxis uses from the group

**Objects** (paper §3.2, Fig. 6). Type III bilinear group `(G_1, G_2, G_T)` of prime order `q`, the
same `q` as the MSIS modulus (BN254 at `λ = 100`, `q ≈ 2^{253.6}`). Published:

* in `G_1`: the left factors `F_i^{k1} = [π_{k1}(y_i, A_i(τ)) Ω]_1`, the quotient and remainder powers
  `[ζ τ^k]_1` and `[ζ' τ^k]_1` (`k < D ≈ N + ν n_c`), and the cancellation column `[ζ'' y_i]_1`;
* in `G_2`: the right factors `H_j^{leg} = [Ω^{-1}(s_leg(r_j + A_j(τ)) + ϑ_{leg,j}, s_leg(B_j(τ) − y_j))]_2`,
  the search bases `[s_leg]_2`, the quotient, remainder, tie and cross bases, and the `α`-copy of
  every `G_2` element;
* in `G_T`: only `K^α = [ακ]_T`, with the key `κ = γ_{c_key} L_ρ(τ)`.

The masked message is `m ⊕ H_key([κ]_T)`. The generators are given to the adversary.

**Honest operations** (Fig. 7):

* MSMs in `G_1` and `G_2` with **full-size `F_q` coefficients**: the weights `ξ_c(w)`, the QAP
  quotient and remainder coefficients `h_{key,k}`, `h_{oth,k}`, `R_{w,k}`, and the cancellation
  polynomials `x^ι_{a,e}`;
* 284 pairings in four sums;
* `F_q`-scalars and additions in `G_T`, including the multiplication by `ξ_key(w)^{-1}`;
* a baby-step giant-step search for `t` with `t · Ψ^α = Λ'` over `|t| ≤ B`, which needs a canonical
  *name* for each `G_T` element (the oracle `name` of Definition 3.1, hashed fingerprints in §6.3);
* the hash `H_key([κ]_T)`, which again needs a canonical encoding of a nonzero `G_T` element.

The encryptor knows every exponent, so a *private-key* encoding suffices. The decryptor never
forms the table: it pairs factors already combined with `w`.

**What the GGM restricts** (Lemmas B.3, B.4, B.12; Fig. 11). Every element that the adversary forms
without guessed labels is a known expression:

* in `G_1` and `G_2`, a linear form in the published elements;
* in `G_T`, a bilinear form `Σ D_ab e(a, b)` plus `D_K K^α`.

Each comparison asks whether such an expression equals `χκ`. Multiplied by `ϖ = Ω_22 ζ ζ' ζ'' ε`,
it is a polynomial of degree at most `d_f = 3D + 2n + 2K_1 + 6` in the hidden coins. The
"allowed" successes are exactly:

* (a) formal identities;
* (b) Schwartz-Zippel coincidences, each with probability at most `ε_f ≈ d_f/q`;
* (c) identities in all coins but the search vector `r`.

The view lemma B.4 reads case (c) as a *usable stack*. Each cell matrix `W_c` is symmetric (the
symmetry term) and passes the tests (QAP criterion). The stack satisfies the ties (mask terms), the
key cell's corner is `χ`, and the adversary must have supplied `u_c = W_c r` for every cell. Such
a comparison succeeds with probability at most `gp(W) ≤ |range|^{−rank W}` (Lemma 4.5; the same
counting as `AdvancedEncryption.WE.RankGap.card_solutions_le`). Two Type III facts are used
implicitly: there is no `G_1 × G_1` product, and no degree above 2.

**Where MSIS enters, and whether it is post-quantum.** MSIS enters only for *heavy* stacks
(`gp > θ ≈ 2^{−201}`), which have rank at most 3. Lemma B.6 shows that a usable heavy stack whose
row space contains no kernel vector of the forms is a combination of honest stacks, so a witness
can be extracted. Otherwise a kernel vector `v` has `gp(vᵀ) > θ`. The inverse theorem (B.7) and
`LIFT` (B.9, using `24β⁴ < q³`) then turn `v` into an MSIS solution with `‖x‖_∞ ≤ β ≈ 2^{187.3}`
over `R_q` (`d_R = 64`, `k = 71`). Theorem 5.9 itself assumes no hardness.

This part is **already post-quantum**: module lattices, with a classical estimate of `2^{103.5}`
from the lattice estimator. Quantum sieving lowers this by roughly the ratio `0.257/0.292` of the
exponents, to about `2^{91}`; this is our estimate, not the paper's. But the MSIS modulus *is* the
group order. A post-quantum substitute must therefore have plaintext space `F_q` with
`q ≳ 2^{250}`. The conditions (P3)-(P4) force `q ≳ 2^{277}` at `λ = 128` (§5). Every
post-quantum weakness lies in the group part.

## 2. Candidate post-quantum substitutes (before §3's attack)

1. **Isogenies.**
   * Pairings on supersingular or isogeny curves are ordinary elliptic-curve pairings, so Shor
     breaks them.
   * Regular group actions (CSIDH) have no addition of two hidden elements; that is the
     parallelization problem. Praxis is then not even *correct*: its decryptor sums hidden
     `G_1` elements. See `pq-we-non-lattice-algebras` §1, whose argument for rank-gap WE applies
     verbatim.
   * Weil pairings on smooth torsion have easy discrete logarithms.
   * Verdict: dead.
2. **BGG+/GSW "bilinear" products.** `sᵀ(A_i G^{-1}(A_j) − x_i x_j G)` needs one factor's plaintext
   *in the clear*, but Praxis pairs two hidden vectors (`y` in `G_1` with `r + A(τ)` in `G_2`). A
   GSW⊗GSW product hides both factors but needs the secret key to test. Releasing a test for
   adversary-chosen bilinear combinations is a compute-and-compare / lockable obfuscation for
   *all* bilinear functions, which is iO-adjacent and not known from LWE. Verdict: no bilinear map.
3. **GGH15 with two levels (`A_0 → A_1 → A_2`).** Level-1 secrets must be short, since the product
   noise `S_1 E_2` must stay small. So `G_1` cannot hold full-size `F_q` plaintexts such as `y_i`.
   Bit or CRT embeddings break `F_q`-linearity, so Dec's MSMs no longer act on plaintexts. The
   γ⊗-GGH15 proofs from LWE (CVW18, see `pq-we-multipass-ggh15` §5) cover products along a fixed
   chain with small random plaintexts, not adversary-chosen bilinear forms over structured `F_q`
   values. Verdict: plaintext mismatch; no proof shape.
4. **GGH13 or CLT13 with index set `{1}, {2}, {1,2}`.** These fit: the plaintext ring is
   `R/gR ≅ F_q`, or one CLT slot. On zeroizing and annihilation attacks, Praxis is unusually
   favorable.
   * On a false statement, an efficient adversary meets **no nontrivial zero at any level**,
     except a coincidence (`ε_f ≈ 2^{−230}`), a light-stack guess (`≤ θ`) or an MSIS break.
     This is Lemma B.4(e) in `G_1`/`G_2` and Lemma B.12 at the top.
   * So the attacks that need top-level zeros (CHLRS15, HJ16, MSZ16, statistical zeroizing) and
     those that need low-level encodings of zero have nothing to work on. Linearization of
     zero-test outputs likewise has no zeros to linearize.
   * The remaining classical threat is lattice reduction on the encodings themselves. Two GGH13
     encodings at one level give an NTRU instance `c_1/c_2`. Dec's MSMs have `D` terms (`2^{22}` in the paper's instance, about `2^{14}` for our circuit)
     with `F_q` coefficients (or published bit-decomposed powers), so `log Q ≳ 2 log q + 2 log(terms·noise)`,
     about 600-700 bits. That is deep in the overstretched-NTRU regime (Kirchner-Fouque 2017;
     Ducas-van Woerden 2021), which forces the ring dimension to roughly `10^6`-`10^7`. This is
     an order-of-magnitude estimate, not an estimator run.
   * Verdict: classical security plausible but heuristic (no reduction to a standard problem), and
     **quantumly dead by §3**.
5. **Any noisy encoding whose test is only a zero test** (no names). This is the only shape that
   §3 leaves open. With no names, the search cannot use baby steps and giant steps, and the key
   must leave through zero tests: publish `C_i = [κ + m_i ρ_i]_T` and test `C_i − [κ]_T`.
   `zeroTest_search_card_le` shows that each zero test of `a Λ' + b Ψ` checks a single candidate.
   At `λ = 128` and range `g ≈ 2^{64.6}`, the search therefore needs about `1.6 · g √(N/24) ≈ 2^{69}`
   zero tests for `N ≈ 4224` (`r(w)` sums about `N/2` box entries). No such encoding is known (§3.3).

## 3. The decryption functionality admits a quantum key recovery

**Attack.** Take an instantiation of Praxis by any `(G_1, G_2, G_T)` encoding, with possibly noisy,
non-unique encodings. Assume it supports Dec's operations of §1 with Dec's coefficient envelope,
including canonical names `name(·)` on `G_T` that are injective on plaintexts up to a negligible
fraction of boundary events. BSGS and `H_key` need exactly this. Let `P_0 = [ζ]_1` and
`P_1 = [ζτ]_1` be two quotient powers, and `B = B^{quo}_{c_key} = [γ Z(τ)(τ − ρ)/ζ]_2`. Define

    f(a, b) := name(e(a P_0 + b P_1, B)) = ν(γ Z(τ)(τ−ρ) · (a + bτ)),   (a, b) ∈ F_q².

1. `f` is a sub-computation of Dec's shape: a 2-term `F_q`-MSM in `G_1`, one pairing and a name.
   So its noise lies inside Dec's correctness envelope, and `f` depends only on `a + bτ`. By
   `period_iff_and_ratio`, its periods are exactly the `(a, b)` with `a + bτ = 0`, and any nonzero
   period gives `τ = −a/b`. Shor's discrete-logarithm period finding over `Z_q²` recovers `τ`
   with `poly(log q)` evaluations of `f`. If Dec used only small coefficients over many terms, the
   Regev-style variant (Regev 2023; Ekerå-Gärtner's extension to discrete logarithms) applies to
   `a ↦ name(e(Σ_k a_k P_k, B))` on a small box. The lattice `{a : Σ a_k τ^k ≡ 0}` has
   determinant `q` and short vectors once `d log(box) ≳ log q`, and `τ` is read off as the line
   orthogonal to it mod `q`.
2. Classically, `[κ]_T = (L_ρ(τ) / (Z(τ)(τ − ρ))) · e(P_0, B)`, since
   `e(P_0, B) = [γ_{c_key} Z(τ)(τ − ρ)]_T`, `κ = γ_{c_key} L_ρ(τ)` and `τ ∉ 𝒫`. This uses one
   pairing and one `G_T` scalar, both operations of Dec.
3. Compute `H_key([κ]_T)` and unmask the message.

The attack works on every statement, uses no witness and breaks no assumption. It applies to the
real Praxis (Shor on BN254) **and to every replacement encoding that keeps Dec working**. Without
the QAP (Praxis's step-1 template), the same period finding on any two published elements recovers
their plaintext ratios. With the published generators, it recovers every plaintext.

**3.1 Why weakening Dec does not help.** Dec's MSM coefficients are pseudorandom `F_q` elements:
the weights `ξ_c(w)` come from random forms, and the quotients `h_W` from the QAP. Publishing
bit-decomposed powers `[2^j x]` keeps coefficients binary, but the attacker uses the same powers
with fewer terms (about `2 log q` against Dec's `D`). Noise budgets are monotone in the
coefficients' `ℓ_1` norm, so the attacker always stays inside the envelope.

**3.2 Zeroizing is not the issue.** The attack produces no zero. It needs names of *nonzero*
values. Praxis's zero-freeness (§2.4) therefore defends against the wrong attack.

**3.3 Linear zero tests give names for free.** Suppose the public test is a noisy linear functional
`Z(u) = λ(m) + e(u) mod Q`, accepting iff `|Z(u)| < B_zt`, with honest noise `|e| ≤ B_e ≪ B_zt`.
This holds for GGH13 (`p_zt · u`), GGH15 (`A_0 D_1 D_2`) and CLT13 (`p_zt · u`). Two encodings of
one plaintext differ by an encoding of zero, so their `Z`-values differ by at most `2B_e`. Two
plaintexts `m ≠ m'` differ by a nonzero plaintext, so their values differ by more than `B_zt − 2B_e`.
Hence the high bits `⌊Z(u)/P⌉` with `2B_e < P < (B_zt − 2B_e)/2` are canonical, up to boundary
events of probability about `2B_e/P`, and injective. Such errors on a small fraction of inputs are
tolerated by period finding. So **any degree-2 encoding with a linear zero test is quantumly broken
when used in Praxis**, even if Dec is rewritten to use zero tests only. A name-free encoding needs a
*non-linear* test whose output on nonzero inputs is not a function of the plaintext. No such
degree-2 encoding is known from a falsifiable assumption; constructing one for adversary-chosen
bilinear forms looks at least as hard as the lockable-obfuscation-for-all-bilinear-forms gap of §2.2.

**Quantum cost** (our estimate): about `2·254` group additions per oracle call in superposition,
plus one pairing and one extraction, times `O(log q)` calls. That is polynomial, and for
lattice-noise encodings dominated by ring arithmetic in dimension about `10^6`.

## 4. Can the GGM step be a falsifiable, statement-independent assumption?

The precise assumption that would suffice is the following.

**Assumption (degree-2 Praxis hiding, D2PH[E]).** For an encoding `E`, a statement `S`, and the
polynomial lists `(P_1(S), P_2(S), κ)` in the coins `c` and the box vector
`r ∈ {2, …, g+1}^{N+1}` of Fig. 6, every efficient `A` has negligible advantage in distinguishing
`(E_1(P_1(c, r)), E_2(P_2(c, r)), H(name([κ(c)]_T)))` from the same with a uniform last component.
This is required only for `S` such that **no efficient algorithm outputs a usable heavy stack**
(Lemma B.4's conditions with `gp > θ`).

Its shape:

* **Statement-dependent if instantiated per `S`.** The instance carries the QAP of `S`, which is
  excluded. This is Barrier 3 of `pq-we-rank-gap-lattice-barriers`.
* **Not falsifiable as a uniform family.** The admissibility predicate is not efficiently
  checkable, for two independent reasons.
  * `rankOne_passing_iff_witness` (Lemma 4.3 of the paper, in coordinates) shows that a usable
    rank-one stack of the single-table template exists **iff** `S` is satisfiable. So any
    admissibility check decides SAT.
  * On false statements, heavy rank-≤3 stacks with kernel vectors **do exist**: Boolean `u ≠ u'`
    with equal forms. They are only *hard to find* (MSIS). The admissibility condition is
    therefore itself a computational precondition, "no efficient algorithm finds a heavy usable
    stack".
  * An assumption of the form "if a pre-game is hard then the encoded target is pseudorandom" is
    exactly the **evasive** shape (precondition/postcondition) that our constraints exclude, with
    the same counterexample risk.
  * The classical Boneh-Boyen-Goh uber-assumption avoids this only because all its variables are
    uniform in `F_q`, so admissibility is linear algebra. Praxis's correctness *needs* the small
    box for `r`, since the honest search is over `r(w)`, and that is what makes admissibility
    intractable.
* **Knowledge-type if the GGM is replaced by an algebraic model.** The extractor reads the
  coefficient matrices `D` off the transcript, so the natural standard-model analogue is an
  algebraic-encoding or linear-only assumption (Barrier 1 of `pq-we-rank-gap-lattice-barriers`).
  That is non-falsifiable. For noisy encodings it is also implausible, since the adversary can run
  lattice reduction on the encodings.
* **Hybrid count.** Outside the generic model, Praxis's proof has one computational hop (MSIS,
  statement-independent), and everything else is statistical given the algebraic restriction.
  A polynomial-hop reduction from statement-independent assumptions would put SAT in SZK
  (`pq-we-hybrid-count-barrier`). So the restriction must carry exponentially many hybrids or a
  non-black-box step.
  * Praxis's security is a *global* rank property of a linear space. It has no witness-indexed
    decomposition, and none is visible.
  * The affine-syzygy barrier does not apply: Praxis is not succinct, its ciphertext being about
    `λ²N` elements, longer than `|φ|`.
  * The linear-hop barrier concerns data-only walks with linear decryption functionals. Praxis
    decrypts with a degree-2 functional, which becomes linear only after the pairing, so that
    barrier is suggestive but not literally applicable.
  * Designing a `2^{128}`-hop walk for Praxis is the same open crux recorded in those notes.

**Verdict.** There is no falsifiable, statement-independent assumption on a degree-2 encoding from
which Praxis's security follows with a polynomial reduction. D2PH is the minimal sufficient
statement, and it is evasive-shaped. Moreover §3 makes D2PH **false** for every encoding that
supports Praxis's decryption, against quantum adversaries.

## 5. Concrete costs against the baselines

These are our estimates, scaling the paper's §6.3 formulas to `Def_WE_CircuitSAT`: `N = 128 + 4096`
Boolean unknowns (inputs plus gate outputs), one R1CS constraint `x·y = 1 − z` per NAND gate, and
`λ = 128`.

* **Parameters.**
  * `g ≈ 2^{64.6}` (`g⁸ ≥ 2^{4λ+5}`), `θ < 2^{−257}`.
  * The inverse-theorem and lifting conditions need `β³ ≳ 6 H_3 q²` with `H_3 ≈ 1/(g³θ) ≈ 2^{63}`,
    and `24β⁴ < q³`. Together they give `q ≳ 2^{277}`, so BN254 and BLS12-381 are too small and a
    pairing group of about 300-bit order is needed. This check is ours.
* **MSIS can be dropped for this `N`.** With `n ≥ N + 1` random forms there is no kernel vector at
  all. Lemma B.6 then covers every stack of rank at most 3, so heavy cheats do not exist on false
  statements, unconditionally in the GGM. This costs `n ≈ 4400` forms and a grid with
  `K_1 K_2 = n/2`, `2K_1 + 12K_2 ≈ 2√(24 · 2200) ≈ 460` elements per unknown.
* **Ciphertext:** about `460 · 4225 + 3D + 8n ≈ 2^{21}` group elements, with `D ≈ 1.25 · 10^4`, at
  about 600 bits each: about `2^{30}` bits.
* **Decryption:** BSGS over about `2^{λ/4} N^{1/4} ≈ 2^{35}` `G_T` operations, at about `2^{18}` bit
  operations each, so about `2^{53}`. Encryption is about `2^{46}`.

| Scheme | Premises | Size / work (bits) | Post-quantum |
| --- | --- | --- | --- |
| Brute force (`we-circuitsat-bruteforce-explicit-cost`) | none | `2^{188}` | yes |
| MP2/MP3 (`pq-we-multipass-ggh15`) | LWE, open reroute lemma | `2^{97}` | yes, if the lemma holds |
| Praxis on the circuit, pairing group | bilinear GGM + RO | `2^{30}` ct / `2^{53}` dec | **no** (Shor; §3) |
| Praxis over GGH13 (2 levels) | heuristic | ring dimension about `10^6`-`10^7`; ct about `2^{21} · 2^{33}` = `2^{54}`; dec about `2^{70}`-`2^{75}` | **no** (§3.3) |
| Praxis over a hypothetical name-free degree-2 encoding | no known assumption | at least `2^{69}` zero tests (§2.5) | unknown object |

None of these rows gives an admissible submission: the problem's registry is plain LWE-family
assumptions, and the GGM is not an assumption at all.

## 6. Takeaways for the WE effort

* What Praxis contributes that *is* post-quantum and reusable:
  * the rank-gap counting with a fixed gap and a wide range, which makes search cost
    `2^{2λ/d}` instead of a polynomial range;
  * the QAP factoring, which turns a quadratic table into width-2 factors;
  * weights from an extension field and ties, which give the gap of one versus four with `O(λ²)`
    copies;
  * the MSIS/inverse-theorem argument against heavy cheats.
* The lattice question of `pq-we-rank-gap-lattice-barriers` (a pseudorandom encoding of `sᵀM_j r`
  under a fixed assumption) is unchanged by Praxis. Praxis shrinks the object to be hidden to a
  rank-2 product, but it still needs a hidden bilinear map whose evaluator holds canonical names
  (§3) or, at least, a non-linear zero test (§3.3).
* New, exact facts for later attempts:
  * the admissibility of any per-instance assumption decides SAT (`rankOne_passing_iff_witness`);
  * name-free searches pay the full range (`zeroTest_search_card_le`);
  * canonical names plus `F_q`-linearity give a period-finding oracle (`period_iff_and_ratio`).
  A future degree-2 post-quantum design must avoid all three.

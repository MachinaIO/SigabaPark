---
title: Post-quantum WE - questioning the framing; nine directions checked against every recorded barrier hypothesis, two pushed (certificate-dual encodings, the concrete-regime budget)
refs: [definition:WE, definition:WE_CircuitSAT, note:pq-we-hybrid-count-barrier, note:pq-we-function-hiding-crux, note:pq-we-evaluation-oracle-crux, note:pq-we-affine-syzygy-barrier, note:pq-we-linear-hop-barrier, note:pq-we-reduction-query-flattening, note:pq-we-gap-structure-routes, note:pq-we-escape-routes-verdicts, note:pq-we-non-lattice-algebras, note:we-circuitsat-bruteforce-explicit-cost, theorem:AdvancedEncryption.WE.Hybrid.stat_hops_carry, theorem:AdvancedEncryption.WE.Hybrid.hardAt_chain, theorem:AdvancedEncryption.WE.LinearHop.hop_dichotomy, theorem:AdvancedEncryption.WE.CertDual.dichotomy, theorem:AdvancedEncryption.WE.Concrete.reduction_budget]
tags: [witness-encryption, strategy, barrier]
---
Research-strategy sub-task on `Def_WE_CircuitSAT`: step back from the GGH15 / BGG+ designs, list
genuinely different directions, check each against the *hypotheses* of every recorded barrier, and
push the two best as far as possible. Two lemmas are proved in Lean (complete proofs, Mathlib
only): `AdvancedEncryption.WE.CertDual.dichotomy` (§2) and
`AdvancedEncryption.WE.Concrete.reduction_budget` (§3). Everything else is an informal argument
checked step by step by the submitting agent. Probabilities are subjective estimates of "this
direction yields a submission for `Def_WE_CircuitSAT` from statement-independent, falsifiable
post-quantum premises within a few months of agent work".

## 0. What the definition asks, and what the barriers assume

**The target, re-read from `Def_WE`.** No setup and no CRS. One-bit messages. Correctness
`1 − 2^{-128}` for every `(φ, w, β)` with `rel φ w`. False-statement security
`cost / Adv² ≥ 2^128` for every false `φ` against every explicit *classical* machine, which may
depend on `φ`. Cost `time(Enc) + time(Dec) + descLen`. Statements: NAND circuits with 128 inputs and
`2^12` gates. Deciding the language costs about `2^140` steps (`2^128` assignments times `2^12`
gates; the explicit baseline `we-circuitsat-bruteforce-explicit-cost` is `2^188`, with a recorded
route to about `2^165`). As far as we know, Circuit-SAT algorithms for circuits of size `c n` (here `c = 32`) save only
a fraction of the exponent that decays exponentially in `c`. So a submission is meaningful when its cost is well below
`2^140`; nothing requires it to be polynomial.

**Barrier hypotheses**, labelled for the analysis below.

| Barrier (note) | Hypotheses |
| --- | --- |
| HC: hybrid count, SZK (`pq-we-hybrid-count-barrier`) | HC1 polynomially many hops; HC2 efficiently samplable hybrids; HC3 each hop statistical on NO instances or computational under an assumption that holds for every `φ`; HC4 asymptotic (`NP ⊄ coAM`) |
| GS: gap-structure flattening (`pq-we-gap-structure-routes` §2) | GS1 simulation-type reductions; GS2 samplable `X_0, X_1`, efficient `R`; GS3 polynomially many hops; GS4 asymptotic |
| QF: query flattening (`pq-we-reduction-query-flattening`) | QF1 black-box reduction; QF2 certifiable queries (Y), (N); QF3 asymptotic (`coNP ⊄ AM`) |
| FH: function-hiding crux (`pq-we-function-hiding-crux`) | FH1 witness-indexed walk; FH2 only the function inside a key changes along it (informal) |
| EO: evaluation-oracle crux (`pq-we-evaluation-oracle-crux`) | EO1 decryption has the BGG+ shape "constrained key plus master function" |
| SY: affine syzygy (`pq-we-affine-syzygy-barrier`) | SY1 data-only; SY2 constant-degree noisy-linear decryption; SY3 witness-indexed local hops; SY4 succinct ciphertext; SY5 planted PRG statements of size `K·|Prg|` with `K ≫ N` |
| LH: linear-hop kill accounting (`pq-we-linear-hop-barrier`) | LH1 data-only; LH2 linear decryption; LH3 witness-indexed local hops; LH4 URR (A) or additive independent (B) hops; LH5 planted statements with `K ≫ N` |

**Observation 0 (concrete vacuity).** At the fixed size of `Def_WE_CircuitSAT` *no* recorded
barrier is a theorem:

* HC, GS and QF conclude "UNSAT has a cheap AM protocol". UNSAT on 128 inputs and `2^12` gates is
  decidable in about `2^140` steps, so the conclusion is false only when every sampler and
  reduction runs well below that. By §3 a proof may afford reductions far above it.
* SY and LH plant `K` PRG witnesses in a statement of size about `K · |Prg|`. A PRG stretching
  `≥ 128`-bit seeds needs some hundreds of NAND gates at least, so `K` is at most a few tens at
  `2^12` gates, and the conclusions (`N ≳ K`) say nothing for any ciphertext of more than a few
  dozen field elements.
* FH and EO are informal design observations, not impossibility results.

The barriers are therefore *design lessons*: they say which proof shapes fail asymptotically and so
are unlikely to have a concrete instance. A direction counts as escaping a barrier below when its
proof shape violates one of the hypotheses, not merely because the parameters are fixed.

## 1. Directions

| # | Direction | Breaks | First concrete step | p |
| --- | --- | --- | --- | --- |
| D1 | **Certificate-dual encodings**: pick the NP-complete encoding whose *unsatisfiability certificates are linear* (Nullstellensatz / polynomial-calculus refutations) so that LWE-type noisy-linear ciphertexts are perfectly hiding on certified-false statements | its statistical part is consistent with every barrier (a promise problem in SZK); completing it needs HC3 (statement-dependent) or HC1 (D3) | the dichotomy lemma (§2, proved) and a cryptanalysis of short pseudo-solutions | 1% |
| D2 | **Non-black-box proofs** (use the adversary's code) | QF1; GS1 only if the hop's indistinguishability holds on NO instances alone | none known: HC bites every proof whose hops are valid for all `φ`, black-box or not, so a non-black-box proof must make a *hop itself* statement-dependent while deriving it from LWE through the adversary's code. All known non-black-box techniques serve zero-knowledge simulation, not soundness; knowledge assumptions are not falsifiable | <0.5% |
| D3 | **Hops indexed by algebraic objects**: monomials of a refutation, restrictions (subcubes) of the inputs, Nullstellensatz coefficients | HC1; SY3/LH3/SY5 (the walk depends on a refutation of `φ`, and PRG-planted statements have no short refutations, so the planted coupling has nothing to couple) | the restriction walk of §2.4 | 1% (merged into D1) |
| D4 | **Inefficiently samplable hybrids** in the concrete regime (sampling by `2^140`-step exhaustive search, truth tables) | HC2, GS2 (and makes HC/GS/QF vacuous, Observation 0) | the budget lemma (§3, proved), then a representation computable from a truth table | 1% |
| D5 | **Two assumption families**, each covering the other's barrier | none: FH, EO, SY, LH constrain proof and decryption *shapes*, not the algebra; a family helps only if it supplies function hiding (compact FE), and no post-quantum family does (`pq-we-non-lattice-algebras`) | — | <0.5% |
| D6 | **Relaxations allowed by the exact definition**: huge-but-sub-brute-force sizes, `2^{-128}` decryption error, classical adversaries | SY4/LH5 (non-succinct ciphertexts); nothing else | see below | <0.5% beyond D4 |
| D7 | **Statistical WE at cost `2^{n/2}`** via batch evaluation (Williams-type MA proofs for #SAT) | HC4/GS4 at the concrete size: statistical WE gives an AM protocol for UNSAT of cost polynomial in `Enc`, and MA protocols of time about `2^{64}` are known for #SAT of circuit classes with low-degree arithmetizations (Williams, CCC 2016: sublinear-depth circuits) | a SAT-to-Statistical-Difference sampler pair of cost `2^{64}` for low-depth circuits (none known; deep circuits have arithmetization degree `2^{depth}`) | <0.5% |
| D8 | **Register one minimal statement-dependent assumption** (for example the certificate-dual LWE of §2.6) and let Cryptanalysis AI attack it | HC3 by design (outside the team's statement-independence constraint, inside the Sigaba rules: a premise must only be registered and survive cryptanalysis) | register CD-LWE(D) at `D = 5` (cost about `2^{60}`) | 5% for a credible premise; it would not answer the post-quantum-from-standard-assumptions question |
| D9 | **Mirror encryption**: the same encodings with the roles swapped are decryptable with a *short linear refutation* and perfectly hiding on satisfiable statements (§2.5) | — (encrypts to coNP certificates, not to witnesses) | — | 0% for WE; a sanity check of D1 |

**D6 in detail.** (a) Ciphertexts of size `2^{40}`–`2^{100}` are allowed; this leaves SY4 and LH5
(already the "BGG+ with the statement as attribute" regime) and nothing else. Truth-table tricks
never beat brute force: a canonical form of a function on `k` witness bits has `2^k` entries, and
splitting `w = (u, v)` multiplies the sizes back to `2^128` (§3.3). (b) The adversary is classical,
so pairing-type assumptions are admissible by the definition, but they are statement-independent too
and meet HC; Hair–Sahai's proof is in the generic group model, which `Def_WE` does not model.
(c) A `2^{-128}` decryption error is what lattice schemes already use. (d) One-bit messages and no
setup are what the barriers already assume.

## 2. Top 1: certificate-dual encodings (D1 + D3)

### 2.1 The scheme

Encode `φ` as a polynomial system over `F_q` (`q` prime): one variable per input and per gate
(`V = 128 + 4096 = 4224` variables), the gate constraints `f_g = z_g + x_g y_g − 1` (NAND), the output
constraint `z_out − 1`, and multilinear reduction (`x² = x`). Let `N_D` be the number of
multilinear monomials of degree `≤ D`, and `M_D` the matrix whose columns are the coefficient
vectors of `m · f` for every constraint `f` and multilinear monomial `m` with `deg(m f) ≤ D`
(degree-`D` Nullstellensatz span `NS_D(φ) = range M_D`). Let `t = 1` be the coefficient vector of
the constant polynomial.

* `Enc(φ, β)`: `c = M_D r + e + Δ β t` with `r` uniform, `e` small (entries `≤ B`), `Δ ≈ q / 2`.
* `Dec(φ, a)`: `v_a ∈ {0,1}^{N_D}`, the vector of values of all monomials at the satisfying
  assignment `a` extended to the wires; output the rounding of `⟨v_a, c⟩`.

Correctness: every `m f` vanishes at `a`, so `⟨v_a, M_D r⟩ = 0`, `⟨v_a, t⟩ = 1`, and
`⟨v_a, c⟩ = ⟨v_a, e⟩ + Δ β` with `|⟨v_a, e⟩| ≤ N_D B`; take `q > 4 N_D B`.
Cost about `nnz(M_D) ≈ 4 · 4097 · N_{D−2}` operations plus `N_D` for decryption:

| `D` | 2 | 3 | 5 | 8 | 10 | 13 | 20 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `log₂ N_D` | 23.1 | 33.5 | 53.3 | 81.0 | 98.6 | 124.0 | 179.8 |

### 2.2 The dichotomy (proved: `AdvancedEncryption.WE.CertDual.dichotomy`)

For a field `K`, a finite module `U`, `L : U → V` linear and a target `t`:

1. if `t ∈ range L`, the law of `L u + e + β t` (uniform `u`) does not depend on `β`;
2. if `t ∉ range L`, some functional `h` has `h ∘ L = 0` and `h t = 1` (Fredholm alternative);
3. every `h` with `h ∘ L = 0` gives `h(L u + e + β t) = h(e) + β h(t)`.

Consequences for the scheme:

* **Perfect security on certified-false statements**: if `φ` has a degree-`D` Nullstellensatz
  refutation over `F_q` (`1 ∈ NS_D(φ)`), the ciphertext is independent of `β`. No assumption.
* **Exact attack surface elsewhere**: if `1 ∉ NS_D(φ)`, the pseudo-solutions `h` (degree-`D`
  pseudo-expectations) exist by item 2, and by item 3 *any short one decrypts*. Security on such
  `φ` is exactly "LWE with the statement's matrix `M_D(φ)` and no short vector in the affine
  lattice `{h : h M_D = 0, h(t) ≠ 0} (mod q)`". This is the "induced lattice gap" of
  `pq-we-gap-structure-routes` §4, now as an exact dichotomy, and it is statement-dependent (HC3).
* **No assumption needed on YES instances**, as usual: the witness *is* a short pseudo-solution
  (`v_a` has `0/1` entries).

So the scheme is a statistical WE for the promise problem "satisfiable" vs "degree-`D` refutable",
consistent with HC (a promise problem in SZK). Algebraic proof systems are the natural LWE-friendly
unsatisfiability certificates: the certificate *is* a linear relation, and noisy-linear encodings
hide exactly what lies in a span. The NP side is the dual side.

### 2.3 Why the statistical part cannot cover all false statements

Every false statement is refutable at degree about `128 + O(1)` (each wire is a polynomial in the
inputs), but `N_{130} ≈ 2^{833}`. Known degree lower bounds (polynomial calculus degree `Ω(n)` for
random 3-CNF, Tseitin formulas in other characteristics, the pigeonhole principle) give false
128-input circuits that need degree `c · 128` for a constant `c`; at `c = 0.1` that is `D ≈ 13`,
`N_D ≈ 2^{124}`, no better than brute force. A uniform small `D` is therefore impossible, and the
statistical scheme covers only a sub-promise.

### 2.4 Restriction-indexed walk (D3)

Split the inputs into a prefix of `h` bits and the rest; let `χ_u` be the multilinear indicator of
prefix `u` (degree `h`), so `t = Σ_u χ_u`. Hybrids `H_k: c = M_D r + e + Δ β Σ_{u ≥ k} χ_u`,
`k = 0 … 2^h`. By item 1 the hop `k → k + 1` is perfect iff `χ_k ∈ NS_D(φ)`, which holds when the
restriction `φ|_k` is refutable at degree about `D − h`. This walk violates HC1, SY3, SY5, LH3 and
LH5 (it is indexed by restrictions, and its hops exist only through refutations). But:

* when every hop is perfect, the walk is only a decomposition of the one statistical hop
  (`Σ_k χ_k = t ∈ NS_D`), so it buys nothing;
* when hop `k` is not perfect, by item 2 there is a pseudo-solution `h_k` with `h_k(χ_k) = 1`, and the
  hop needs "no short `h ⊥ NS_D` with `h(χ_k) ≠ 0`": statement-dependent again, now on the
  restricted statement. The walk localizes the assumption; it does not make it statement-independent.

The walk would need an *LWE hop* at the non-refutable restrictions, i.e. a statement-independent
reason why `M_D r + e + Δχ_k` and `M_D r + e` are indistinguishable when `φ|_k` is false. By item 3
the only distinguishers that use linear structure are pseudo-solutions, so such a reason would be a
worst-case hardness result for finding short pseudo-solutions, which LWE does not provide (the
matrix `M_D(φ)` is not uniform).

### 2.5 Mirror check (D9)

Publish `⟨s, m f⟩ + noise` for every column of `M_D` and `⟨s, t⟩ + noise + Δβ`. A short
refutation `λ` (`M_D λ = t`) decrypts by `c_0 − Σ λ_j c_j`; on a satisfiable `φ`, `t ∉ range M_D`
(item 2), so `⟨s, t⟩` is uniform and independent of the other values: perfect hiding. Noisy-linear
encodings are *linear-certificate* devices on both sides. The asymmetry WE needs (a non-linear
witness, a linear security reason) is exactly what they do not have.

### 2.6 Where Top 1 ends, and the next steps

* **Assumption CD-LWE(`D`)** (for D8): for every false 128-input `2^{12}`-gate circuit `φ`,
  `(M_D(φ), M_D r + e)` and `(M_D(φ), M_D r + e + Δ t)` are indistinguishable. Falsifiable per
  statement and simple to state; statement-dependent.
* **First cryptanalysis target**: short pseudo-solutions. Sherali–Adams-type local distributions
  give pseudo-expectations with dyadic values; `2^D h` is then integral with `(2^D h)(t) = 2^D`, and
  it decrypts if `2^D ‖h‖₁ B < q / 4`. Whether local distributions exist for the *circuit* encoding
  (consistency along the gates, not only on clauses) is unverified. For small `D` the PC closure is
  nearly free and `{0,1}`-valued pseudo-solutions look easy to build; we expect CD-LWE(`D`) to be
  false for `D ≤ 3`. A Lean statement of "short pseudo-solution ⇒ distinguisher" follows from item 3.
* **Probability** of a statement-independent proof through this route: about 1%.

## 3. Top 2: the concrete regime (D4 + D6)

### 3.1 Budget (proved: `AdvancedEncryption.WE.Concrete.reduction_budget`)

If an adversary of cost `c ≥ 1` has advantage `adv ≤ Σ_{i<L} ε_i`, and each hop `i` is turned by a
reduction with additive overhead `T` into an attacker on a premise of strength `P`
(`2^P ε_i² ≤ c + T`), then `2^P adv² ≤ L² (1 + T) c`. So false-statement security is
`P − 2 log₂ L − log₂(1 + T)` bits. (`AdvancedEncryption.WE.Hybrid.hardAt_chain` is the case
`T = 0`.) With `L = 2^{128}` hops and `λ = 128`, a premise of `P = 640` bits allows reductions and
samplers of `2^{256}` steps. LWE at 640 bits costs only polynomially larger parameters. Hence:

* every hybrid may brute-force the statement (`2^{140}`), any `2^{128}`-entry truth table, or any
  `2^{200}`-step computation;
* by Observation 0, HC, GS and QF then say nothing.

### 3.2 Complexity leveraging is useless for WE

In a non-interactive game with the statement fixed in advance, the adversary makes no choice for a
reduction to guess. The reduction knows all of the ciphertext randomness except the embedded
challenge. Exponential work can therefore (a) attack the challenge, which is the premise itself and
is already priced in `P`; or (b) compute functions of `φ` and of its own randomness. About `φ` it
learns only "`φ ≡ 0`", which the proof already knows (`pq-we-gap-structure-routes` (b)). So the
only use of exponential time is **canonicalization**: computing, from the truth table of the
decryptor's function `F` (`pq-we-evaluation-oracle-crux`), an object whose law depends on the
table alone. "Two-tier" designs (a component of strength 160 bits, breakable by the reduction but
not by the adversary) reduce to case (a): the weak component is part of the premise.

### 3.3 Canonicalization needs compression, i.e. XiO for one family

`pq-we-escape-routes-verdicts` §4 left one case open: a representation `O` of
`F = F_{s,A}` that depends on exponentially many table entries yet is computable from the table in
time `T` without recovering `s`. Adding the size constraint: `|O| ≤ cost ≪ 2^{140}` while the table
has `2^{128}` entries, so `O` compresses the table by a factor `≥ 2^{28}`, and the hop
`O(F) ≈ Sim(table(F))` is exactly an *exponential-simulator* (virtual-gray-box) obfuscation of the
family `{F_{s,A}}` with non-trivial compression, i.e. exponentially-efficient iO restricted to that
family. Splitting `w = (u, v)` does not help: prefix-constrained keys `k_u` for `F(u, ·)` cost
`2^{64}` in total, but each `k_u ≈ k'_u` is the same crux on 64 bits, and the canonical form of each
`F(u, ·)` has `2^{64}` entries, `2^{128}` in all. For all circuits, XiO with non-trivial compression
plus LWE gives iO (Lin–Pass–Seth–Telang); for the single family `F_{s,A}` at one size that
implication is not known, and this is the narrowest form of the target that we can state:

> **Open target (XiO-F).** A representation of `w ↦ ⌊sᵀ A_{U_w}⌉_p` (`w ∈ {0,1}^{128}`, `A`
> public) of size `≤ 2^{100}`, together with a sampler `Sim` running in time `≤ 2^{250}` on the
> truth table and `A`, such that `O(s, A) ≈ Sim(table, A)` under LWE at `≤ 640` bits.
> By §3.1 and `pq-we-evaluation-oracle-crux`, XiO-F gives `Def_WE_CircuitSAT` from LWE with a
> three-hop proof.

**Probability** about 1%. It is as hard as the evaluation-oracle crux, but it is the formulation in
which every asymptotic barrier is gone and only the object is missing.

## 4. Verdict

* At the concrete size no recorded barrier is a theorem (Observation 0); they are design lessons.
* The genuinely different routes (D1/D3 certificate-dual encodings, D4 inefficient hybrids, D7
  statistical `2^{n/2}` WE) each escape the complexity barriers' hypotheses. Each still ends at
  one missing object: a statement-independent reason why short pseudo-solutions do not exist (D1/D3),
  a compressing exponential-simulator representation of one PRF family (D4, XiO-F), or a
  `2^{64}`-cost SAT-to-SD reduction (D7).
* The exact dichotomy of §2.2 explains why noisy-linear encodings handle linear (coNP-side)
  certificates perfectly and the NP side only through the absence of short dual vectors.
* Recommended next steps: (1) cryptanalysis of CD-LWE(`D`) for `D ≤ 5` (short pseudo-solutions for
  circuit encodings); (2) if the team admits a registered statement-dependent premise (D8), a
  submission from CD-LWE at `D = 5` costs about `2^{60}`; (3) XiO-F as the single statement of the
  remaining open problem for the post-quantum route.

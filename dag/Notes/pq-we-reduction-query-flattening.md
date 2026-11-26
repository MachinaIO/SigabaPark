---
title: Escape (c) - laconic zero-knowledge arguments and rewinding reductions - flattens to coAM whenever the reduction's queries are certifiable; what is left open
refs: [definition:WE, definition:WE_CircuitSAT, note:pq-we-gap-structure-routes, note:pq-we-hybrid-count-barrier, theorem:AdvancedEncryption.WE.Hybrid.stat_hops_carry]
tags: [witness-encryption, barrier, strategy]
---
Design-AI sub-task (f): escape (c) of `pq-we-gap-structure-routes`. Can WE security for
`Def_WE_CircuitSAT` be proved from a statement-independent falsifiable assumption (LWE and its
variants, LPN, isogenies, Goldreich's PRG) by a reduction that is not of simulation type, for
example one that rewinds the adversary or queries it on malformed ciphertexts? Through
Liu–Mazor–Pass this is the question of proving soundness of a laconic zero-knowledge argument by
such a reduction. This note (1) states the equivalence exactly, (2) checks where Gentry–Wichs
stops, (3) proves a flattening theorem that covers rewinding and correlated-query reductions, and
(4) states what is left. The arguments are informal complexity arguments; one counting step is the
Lean theorem `AdvancedEncryption.WE.Reduction.steered_le_card_mul_guess` (complete proof submitted in SigabaPark PR #37).

Sources read in full text (kept out of the DAG): Liu–Mazor–Pass, *On Witness Encryption and
Laconic Zero-Knowledge Arguments*, ECCC TR24-194 (CRYPTO 2025), cited by Hair–Sahai
(arXiv 2609.18275) as [LMP25]; Gentry–Wichs, *Separating Succinct Non-Interactive Arguments From
All Falsifiable Assumptions*, ePrint 2010/610 (version of June 6, 2013).

## 1. The LMP equivalence, exactly

**Definitions used by LMP (§2).** Interactive *argument* (Def. 2.1): completeness `c(n)` for every
`x ∈ L` and witness; soundness error `s(n)` against every non-uniform polynomial-time prover
`P*`, for every *fixed* `x ∉ L` (static soundness: the statement is given, not chosen by `P*`).
`ℓ`-laconic (Def. 2.2): total prover communication at most `ℓ(|x|)`; *laconic* means
`ℓ = O(log n)`. SHVZK (Def. 2.3): a PPT simulator `S(x, r)`, given the verifier's coins `r`,
whose output is computationally indistinguishable (non-uniform) from the honest verifier's view
with coins `r`. WE (Def. 2.4): correctness `Pr[Dec(Enc(x, b), w) = b] ≥ 1 − 2^{-n}` (not perfect);
security against non-uniform distinguishers for every fixed `x ∉ L`.

**Theorem 3.1 (LMP).** For every `L ∈ NP` the following are equivalent:

1. WE for `L` (resp. statistically secure WE);
2. an efficient-prover `ℓ`-laconic SHVZK argument (resp. proof) for `L` with
   `c(n) − s(n) ≥ 1/poly(n)` and `ℓ = O(log n)`;
3. for every efficiently computable `ℓ(n) ≥ 1`, an efficient, deterministic-prover, `ℓ`-laconic,
   **two-round**, statistical-SHVZK argument (resp. proof) with completeness `1 − 2^{-n}` and
   soundness error `2^{-ℓ} + negl`.

(2 ⇒ 1) is Cor. 5.2 (weak WE from the protocol, then amplification by weakly verifiable puzzles,
Goldreich–Levin and majority, Prop. 4.2); (1 ⇒ 3) is Thm. 6.1, the protocol of
Komargodski–Moran–Naor–Pass–Rosen–Yogev: the verifier sends `Enc(x, b)` for a random bit `b` and
accepts iff the prover returns `b`. Both directions are **black-box in the adversary**: Lemma 5.6
turns a WE adversary `A` into the cheating prover `R^A` that answers each prover round with
`A(x, i, π_{[i−1]}, v)` for a fresh `v`; Thm. 6.1's soundness is WE security applied to the
prover's single answer.

**Consequence for escape (c).** By item 3 with `ℓ = 1`, "a laconic argument whose soundness has a
rewinding reduction" is, up to black-box equivalence, a WE scheme whose security has a reduction
that queries the adversary (a predictor `c ↦ b`) on many verifier messages. "Rewinding" the one-bit
prover *is* querying the predictor on other messages; there is no other state to rewind. The rest
of this note works with WE and its predictor.

## 2. Gentry–Wichs does not apply, and where its proof stops

GW (Thm. 5.1 with Lemma 4.1) rule out black-box reductions from any falsifiable assumption to the
**adaptive** soundness of (designated-verifier, slightly) succinct non-interactive arguments,
assuming sub-exponentially hard subset-membership problems. They say explicitly (§1.1,
"Extensions and Limitations") that succinct **two-round arguments with static soundness** are a
weaker primitive and that "we do not know how to extend our separation to the former primitive,
and it remains as an interesting open problem". Item 3 above is a primitive of that kind (two rounds,
static soundness, one prover bit; the verifier's message depends on `x` and verification needs the
verifier's coins). GW's separation does not cover it, and we know no other theorem that covers
escape (c).

The step that fails: GW's simulatable adversary answers **each** query `crs` with a fresh false
statement `x̄` and a fake proof `π̄` from their Lemma 3.1 (indistinguishability with auxiliary
information, loss `2^{|π|}`), and the proof of Lemma 4.1 is a hybrid over queries, one fresh
statement per query. In WE (and in static soundness) the reduction fixes `x` and every query is
about the same `x`. Applying Lemma 3.1 to all `q` answers jointly costs `2^q` in the
distinguisher size, and the min-max "lie" it produces is a function of the whole query sequence,
not a stateless oracle `c ↦ A(c)`, which a reduction may query repeatedly in any order. With
`q = poly(n)` neither defect is repairable by choosing a harder subset-membership problem.

## 3. A flattening theorem for certifiable queries

`pq-we-gap-structure-routes` §2 flattens single-query simulation-type reductions into SZK. The
following extends that to reductions with any number of adaptive queries (rewinding, correlated
or Goldreich–Levin-type queries, search-to-decision), provided every query is one whose correct
answer can be *certified*. The idea is the converse of the GW route: instead of simulating the
inefficient adversary on a true statement, let Merlin supply its answers with certificates.

**Setting.** `(Enc, Dec)` WE for `L ∈ NP`; a falsifiable assumption in GW's sense (efficient
challenger `C`, threshold `c`; LWE with `c = 1/2`, search problems with `c = 0`) that holds against
non-uniform polynomial-size circuits. `R` is a black-box reduction: an efficient oracle machine such
that for every `x ∉ L` and every (possibly inefficient) oracle `A` with WE advantage at least `1/4`
on `x` (advantage as in `Def_WE`: `|Pr[A(Enc(x, 0)) = 1] − Pr[A(Enc(x, 1)) = 1]|`; the ML predictor
has advantage `SD − negl`), `R^A(x)` wins against `C` with probability at least `c + η(|x|)`, `η` an inverse polynomial.

**Certifiable answers.** An NP relation `Cert(x, c, a)` ("query `c` has the certified answer `a`")
together with an efficient `O(x, w, c)` such that

* **(Y) forced on true statements:** if `(x, w)` is in the relation and `Cert(x, c, a)`, then
  `a = O(x, w, c)`;
* **(N) good on false statements:** for every `x ∉ L` with `SD(Enc(x, 0), Enc(x, 1)) ≥ 1/2`
  there is an oracle `A_x` with advantage at least `1/4` such that, except with probability
  `η/2`, every query `c` of `R^{A_x}(x)` satisfies `Cert(x, c, A_x(c))`.

Main instance: `Cert(x, c, a) := ∃ρ ∈ Typ, Enc(x, a; ρ) = c` (the certificate is the encryption
coins, `Typ` a set of typical coins, e.g. noise within its bound, of probability `1 − negl`),
`O = Dec`, `A_x` = the maximum-likelihood predictor for the typical-coin laws of `Enc(x, 0)` and
`Enc(x, 1)` (advantage `SD − negl`; its answer `a` on a typical ciphertext always has a typical
preimage under `a`). (Y) holds when `Dec` is correct on *every* typical-coin ciphertext, as in lattice
schemes with bounded noise (otherwise replace (Y) by "the run `R^{Dec}(x)` never queries a
typical-coin ciphertext that `Dec` gets wrong, except with negligible probability": runs agree up
to the first such query; this is a hypothesis on `R` (it must not *construct* typical-coin
ciphertexts that `Dec` gets wrong), not a consequence of the correctness bound). (N) says: on false statements the reduction only queries
ciphertexts that some typical encryption produces. Queries that are honest
ciphertexts in every branch of the challenge satisfy it: rewinding the one-bit prover of LMP item 3
on honestly sampled verifier messages, and random-self-reducible or Goldreich–Levin-type queries.
Queries that leave the typical support in some branch of the challenge do not (see §4). Other instances: `Cert` can certify a nearby typical
ciphertext within `Dec`'s decoding radius (if `Dec` provably decodes there), or a syntactically
malformed query with a fixed answer.

**Theorem (informal).** Under (Y) and (N), `L̄ ∈ AM`. For `L` = Circuit-SAT this collapses the
polynomial hierarchy (Boppana–Håstad–Zachos).

**Proof.** Merlin chooses a branch.

* *Statistical branch* (`SD(Enc(x, 0), Enc(x, 1)) ≤ 1/2`): with WE correctness, true statements
  have `SD ≥ 1 − 2^{-n+1}`. The promise problem "SD ≥ 1 − 2^{-n+1}" vs "SD ≤ 1/2" satisfies
  `α² > β`, so it and its complement are in SZK (Sahai–Vadhan; SZK is closed under complement)
  `⊆ AM`.
* *Reduction branch:* Arthur draws coins for `m` independent runs of `C` interacting with `R(x)`
  and sends them. Merlin returns, for every query `c` of every run (replayed with his own answers),
  an answer `a` and a certificate of `Cert(x, c, a)`. Arthur replays all runs; a run with a
  missing or invalid certificate counts as lost; Arthur accepts iff at least `(c + η/4) m` runs are
  won.
  * `x ∉ L`, `SD ≥ 1/2`: honest Merlin answers with `A_x`; by (N) and the reduction's guarantee
    each run is won with probability at least `c + η/2`. Chernoff.
  * `x ∈ L` with witness `w`: by (Y) every certified answer equals `O(x, w, c)`, so every run that
    is not lost is exactly a run of `R^{O(x, w, ·)}(x)`, an efficient machine with advice `(x, w)`.
    Merlin's only freedom is to lose runs. Each run is won with probability at most `c + negl` by
    the assumption, independently across runs (Merlin cannot change answers). Chernoff. ∎

Asymptotics: "`≤ c + negl` for every large true `x`" uses that the scheme's security parameter is
polynomially related to `|x|`; an infinite sequence of true statements violating it would give a
non-uniform breaker with advice `(x, w)` (finitely many exceptions are hard-wired into Arthur).

Merlin's answers do not depend on Arthur's secrecy, so sending all coins at once is fine, and
adaptivity of `R` costs nothing: the protocol is two-message and public-coin.

**Bounded uncertified queries (search-type assumptions).** Suppose (N) is weakened: on false
statements, each run makes at most `k` queries outside `Cert`, answered arbitrarily (`R` must
work for every answer there). Arthur then lets Merlin answer at most `k` queries per run without
certificate (a run with more counts as lost). Answers are one bit. On a true statement Merlin now chooses an answer pattern `g` from a set of size
`N ≤ Σ_{j≤k} C(q, j) 2^j` (`q` queries per run), after seeing all coins. By
`AdvancedEncryption.WE.Reduction.steered_le_card_mul_guess`, he wins a run with probability at most
`N` times that of the efficient run that guesses the pattern, which wins with probability
`≤ c + negl`. For `c = 0` (search assumptions: search-LWE, SIS, one-wayness) and `N = poly`
(`k = O(1)`, or `k = O(log n / log q)`), this is still negligible and the theorem holds. For
decision assumptions (`c = 1/2`) the bound is useless, and the extension fails.

**Relation to the earlier barriers.** `stat_hops_carry` and the SZK argument flatten
statistically faithful single-query simulations; the theorem above flattens multi-query reductions
whose queries are certifiable. Neither covers the other: a Regev-type hop whose embedded challenge
gives honest ciphertexts under `X_0` and uniform (off-support) ones under `X_1` violates (N) but is
covered by the SZK argument. Multi-query reductions of that kind are covered by neither (§4).

**Concrete setting.** The AM protocol runs in time `poly(T_R, T_C, T_Enc)` and its soundness uses
the assumption at cost `T_R + q·T_Dec`. For `Def_WE_CircuitSAT` (128-bit witnesses) UNSAT is
decidable in `2^128 · |φ|` anyway, so, as in `pq-we-gap-structure-routes` §3, the theorem forbids
only reductions fast enough to give AM protocols for 128-variable UNSAT that beat the known ones
(Williams, CCC 2016: MA protocols for #SAT of sublinear-depth circuits in about `2^{n/2}` time). A reduction spending about `2^128` (escape (b)) is not
excluded.

## 4. What escapes, and the sharpest open target

**What the theorem does not cover, and why it matters.** A query built from the reduction's own
coins carries no information, since `R` already knows its answer. Useful queries come from the
challenger's challenge. For a decision assumption the usual embedding gives honest ciphertexts under
`X_0` and pseudo-ciphertexts outside the typical support under `X_1` (e.g. a uniform vector in place
of an LWE sample). Such queries violate (N) in the `X_1` branch. The flattening really fails
there: Arthur's coins fix the branch, so on a true statement Merlin may call any `X_1`-branch query
uncertifiable and choose its answer (if `R`'s output is the answer to one query, he wins with
probability `1`). With a single query and statistically faithful hybrids the SZK argument of
`pq-we-gap-structure-routes` §2 covers this case; with several queries it covers nothing.

So the two flattenings together leave exactly the following class, and it is **not exotic**: it is
the generic template of a multi-query reduction to a decision assumption.

> **Open target (c\*).** A WE scheme for Circuit-SAT (equivalently, by LMP item 3, a two-round
> one-bit-prover argument with static soundness) and a black-box reduction `R` from its security to
> a statement-independent **decision** assumption such that, on false statements, `R`
> (i) makes several queries derived from the challenge, at least some of which, under some branch
> of the challenge, lie outside every certifiable answer set satisfying (Y) (outside the typical
> support, beyond what `Dec` provably decodes, not recognizable as malformed in polynomial time),
> and (ii) is not a single statistically faithful simulation hop; while `R` works for every answer
> to the queries of (i).

Multi-query reductions that are statistically faithful (every query close to an honest
ciphertext of an *unknown* bit) but whose queries are not certifiable fall in (c\*) as well: neither
result covers them.

**What (c\*) must still achieve.** In the `X_1` branch the answers to off-support queries are
arbitrary (the reduction works for all of them), so all the distinguishing signal has to come from
the `X_0` branch, where the queries are certifiable, compared with a branch where the answers are
unconstrained. On a true statement the same comparison, with `Dec` answering, must fail (otherwise
`R^{Dec}` breaks the assumption). The statement `x ∉ L` therefore has to change how the
certifiable `X_0`-branch answers relate to the challenge. This is the same statement-dependence
that every recorded WE route needs (`pq-we-evaluation-oracle-crux`), now located in the joint law
of several honest decryptions rather than in one hop.

**Concrete reductions tried during this sub-task**, each falling in a flattened class:

* *Decryption-threshold key recovery* (query `(c_1, c_2 + k·Δ)` to binary-search `sᵀu`): the
  shifted queries are certifiable as long as `Dec` provably decodes them, so (N) holds and the
  reduction flattens. Beyond the decoding radius `R` must work for every answer, so it learns
  nothing there.
* *Dual-Regev embedding* (`u = B r`, `c_2 = t r + b⌊q/2⌋`): a single simulation hop, flattened by
  the SZK argument. The statement does not enter. The missing object is again the
  statement-dependent part of the ciphertext.
* *Using the predictor as a distinguisher between two candidate representations* (`O` versus
  `O'`): one query per hop, statistically faithful on false statements, so the SZK argument
  applies.

None of them is a candidate for (c\*). A candidate would need several challenge-derived queries
whose decryptions, *jointly*, reveal the challenge bit only when `x ∉ L`.

## Verdict

* **No known theorem closes escape (c).** GW leave static two-round soundness open, and our
  flattenings do not cover the multi-query decision-assumption template (c\*).
* **Flattened (`L̄ ∈ AM`, PH collapse for Circuit-SAT):**
  * reductions whose queries on false statements are all certifiable. This includes rewinding the
    laconic prover on challenges it generated itself, and queries that are honest ciphertexts by
    random self-reduction or Goldreich–Levin.
  * against search-type assumptions, reductions with a bounded number (`O(1)`) of uncertified
    queries.
  * single statistically faithful simulation hops (the earlier SZK argument).
* **Open target: (c\*).** Exhibiting a reduction in class (c\*) for *any* NP language outside SZK
  would already be new. Until that exists, escape (c) does not give a concrete design for
  `Def_WE_CircuitSAT`.

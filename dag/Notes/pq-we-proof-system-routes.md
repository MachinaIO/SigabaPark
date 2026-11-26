---
title: WE through proof systems - linear-verification SNARKs, predictable arguments, refutations, witness splitting (verdicts; the compliant lead is 2^(m/2) XWE from LWE)
refs: [definition:WE, definition:WE_CircuitSAT, note:pq-we-reduction-query-flattening, note:pq-we-hybrid-count-barrier, note:pq-we-function-hiding-crux, note:pq-we-evaluation-oracle-crux, note:pq-we-decryptor-attribute-dead-end, note:we-circuitsat-bruteforce-explicit-cost, theorem:AdvancedEncryption.WE.Hybrid.hardAt_chain]
tags: [witness-encryption, strategy, barrier, survey]
---
Design-AI sub-task: build WE for `Def_WE_CircuitSAT` (NAND circuits with `2^12` gates,
128-bit witnesses, `λ = κ = 128`, no setup) through **proof systems** rather than encodings.
Constraints: post-quantum, falsifiable, statement-independent assumptions; no iO, no evasive LWE,
no local mixing. The framing is Liu–Mazor–Pass (`pq-we-reduction-query-flattening` §1): WE is
equivalent to a two-round argument whose prover sends one bit. That bit is the verifier's
*predicted* value, so WE is a predictable argument. The arguments below are informal unless a Lean
theorem is named. Two lemmas are submitted with complete proofs in the same PR:
`AdvancedEncryption.WE.LinearVerif.check_alternative` and
`AdvancedEncryption.WE.LinearVerif.sph_perfect_hiding`.

Sources read in full text (kept out of the DAG): Garg–Hajiabadi–Kolonelos–Kothapalli–Policharla,
*A Framework for Witness Encryption from Linearly Verifiable SNARKs and Applications*, ePrint
2025/1364 ("GHKKP"); Brakerski–Jain–Komargodski–Passelègue–Wichs, *Non-Trivial Witness Encryption
and Null-iO from Standard Assumptions*, ePrint 2017/874 ("BJKPW"). Abstracts only: Jin–Kalai–
Lombardi–Vaikuntanathan, *SNARGs under LWE via Propositional Proofs*, ePrint 2024/956 ("JKLV");
Agrawal–Yadav–Yamada, *Multi-Input ABE and Predicate Encryption*, ePrint 2022/1024 ("AYY").

## Summary

| Route | Verdict |
| --- | --- |
| (1) SNARK with linear verification + hash-proof encryption (GHKKP) | **Excluded.** Security is *extractable* and is proved in the GGM + ROM, with a trapdoor CRS. With falsifiable assumptions, the composition dichotomy below gives `L ∈ BPP`, an SZK-type collapse, or no security at all. |
| (1') lattice designated-verifier SNARGs (decrypt, then quadratic check) | **Excluded.** Not linearly verifiable, and their knowledge soundness rests on linear-only (knowledge) assumptions. |
| (2) predictable arguments (Faonio–Nielsen–Venturi) | **Equivalent to WE**: a reformulation, not a route. |
| (3) short refutations (propositional proof systems, JKLV) | **Escapes the SZK barrier only for a promise problem**, and runs into the function-hiding crux. Brings no concrete gain for 128-bit witnesses. Open target (P3) below. |
| (4) batch / witness splitting | **Only compliant construction found**: BJKPW XWE, encryption time `2^{m/2}·poly` from sub-exponential LWE (via ABE). Compressing an OR is the obstacle, and BARGs compress ANDs. Going below `2^{m/2}` needs multi-input ABE, which exists only heuristically or in the GGM. |
| (5) encryptor-generated CRS | **Harmless** for every route (the encryptor is honest, and a fresh CRS per ciphertext needs only static soundness). It does **not** supply the missing knowledge or extraction step. |

**Best lead:** route (4), the `2^{m/2}` split, as a concrete *non-trivial* submission. Its
concrete cost depends heavily on circuit depth (§4.3). Our estimate puts it within a few bits of
brute force at depth `4096`, and about `2^{20}` below it at depth `≤ 256`.

## 1. WE from linearly verifiable SNARKs (GHKKP), and the composition dichotomy

**What GHKKP do** (§2.1, Construction 2, Theorem 1). A relation `R` is reduced, through a
witness map, to gadget relations with non-interactive arguments of knowledge whose verifier is a
linear system `A_{vk,u}(w, π) = b_{vk,u}` (Definition 5). The ciphertext is
`(s·A, H(s·b) + msg)`, and decryption computes `H((s·A)·π)`. Security (Definition 7) is
**extractable**: an extractor reads the adversary's GGM/RO queries and outputs a witness. The
parameters come from `Gen(λ, N, td)` with a trapdoor. Theorem 1 holds in the GGM + ROM over
pairing groups. The paper says explicitly (footnote 4) that after compressing the relation
"typically all statements are true and hence witness encryption (without extractability) does not
offer any meaningful guarantees". It also notes (§2.1) that by Groth's lower bound, succinct
linearly verifiable arguments for all of NP are infeasible in the pairing setting.

**The algebraic core (Lean).** Over a field `K`, take the check `M π = v` with ciphertext
`(kᵀM, k·v + μ)`:

* `check_alternative`: `(∃π, M π = v) ↔ ∀k, kᵀM = 0 → k·v = 0`. If the check is satisfiable,
  `k·v = (kᵀM)·π` is determined by the ciphertext.
* `sph_perfect_hiding`: if the check is unsatisfiable, then for every `a` the hash `k·v` is
  uniform on `{k : kᵀM = a}`, so `μ` is perfectly hidden.

So the linear template is **perfectly hiding exactly on unsatisfiable checks and
information-theoretically open on satisfiable ones**.

**Composition dichotomy.** Let a statement map `x ↦ (crs, x)` reduce `L` to a "WE-friendly" class
`C` of verification relations, and take the inner WE for `C`. Then:

1. *Statistically sound reduction* (`x ∉ L ⇒ (crs, x) ∉ L_C` except with small probability over
   the encryptor's `crs`), with `C` = linear systems over a field. Solvability is decidable in
   polynomial time, so the encryptor decides `x ∈ L` with bounded error, and `L ∈ BPP`.
   (Concretely, at 128-bit witnesses, the reduction must spend about `2^{128}`.)
2. *Statistically sound reduction* into a class with statistical WE, for example
   "`∃` short `π` with `A π = b mod q`" with the noisy template
   `(kᵀA + e, kᵀb + e' + μ⌊q/2⌋)`. The whole scheme then has a one-hop statistical proof, and
   `pq-we-hybrid-count-barrier` puts `L` in SZK. This matches what is known: the gap versions of
   short-vector problems that such templates hide statistically are in coAM, not NP-hard.
3. *Computationally sound reduction* (every SNARG; with succinct proofs, false `x` typically have
   accepting proofs). Then by `check_alternative`, `(crs, x) ∈ L_C` for most false `x`, and the
   inner ciphertext determines `μ` information-theoretically. Security can only come from the
   hardness of *finding* an accepting proof. A reduction then has to turn a **distinguisher** into
   a **prover**. That is extraction (knowledge soundness, extractable WE), which is non-falsifiable
   in general (Gentry–Wichs), and GHKKP obtain it only in the GGM.

**Post-quantum analogue (1').** The lattice SNARKs with linear-looking verification that we know
of either (a) are designated-verifier, with verification "decrypt the Regev/vector-encryption
answers, then check a quadratic relation of a linear PCP", soundness from linear-only encryption
(a knowledge assumption), and a check that is not linear in the proof; or (b) verify a linear
relation on short vectors, with knowledge soundness from knowledge-type ISIS variants. In (a) not even
the template applies, since the check is not linear. In (b) the noisy template of item 2
decrypts, and security is case 3, i.e. a knowledge assumption. **Verdict: excluded under our constraints.** This is a structural reason, not a gap
in the literature: by the dichotomy, a falsifiable route has to avoid case 3, so it needs
statistical soundness, and items 1–2 then give a collapse.

**Concrete remark.** For `Def_WE_CircuitSAT` the witness is 128 bits, shorter than any SNARG proof.
Succinctness buys nothing here; the only purpose of a proof system would be to make verification
*encryptable*, and the dichotomy blocks that.

## 2. Predictable arguments (Faonio–Nielsen–Venturi)

A predictable argument is one where the verifier can predict the honest prover's reply. FNV show
that predictable arguments are equivalent to WE, predictable arguments *of knowledge* are
equivalent to extractable WE, and the protocols can be collapsed to two rounds. With LMP Theorem
3.1 (`pq-we-reduction-query-flattening` §1) this is the same object as a one-bit-prover two-round
argument. Lattice-based predictable arguments are known for languages with (approximate) smooth
projective hashing: "this LWE ciphertext encrypts `m`", and similar. These languages are defined
statistically, and case 2 of §1 applies to them. **Verdict: a reformulation of the target.** A
lattice predictable argument for Circuit-SAT *is* a lattice WE.

## 3. Statements with short unsatisfiability certificates

**The promise escapes the barrier.** Let `Π_s = (SAT, UNSAT_s)`, where `UNSAT_s` consists of
unsatisfiable circuits with a refutation of size `≤ s` in a fixed propositional proof system
(resolution, Frege, EF). `Π_s` lies in promise-NP ∩ promise-coNP: a witness certifies YES and a
refutation certifies NO. The argument of `pq-we-hybrid-count-barrier`, applied to a WE scheme whose
poly-hop proof uses only `φ ∈ UNSAT_s`, gives `Π_s ∈ SZK`, and that collapses nothing. So **poly-hop
WE for `Π_s` from statement-independent assumptions is not ruled out by any barrier we have**.
JKLV (abstract) do the analogous thing for SNARGs: SNARGs from LWE for languages whose
non-members have propositional refutations, with transparent setup, proof size polylogarithmic in
the refutation length, and super-polynomial lengths handled at bounded space under
sub-exponential LWE.

**Why JKLV's technique does not transfer.** Their soundness analysis opens the cheating prover's
*long* message locally (local assignment generators, "locally unsatisfiable extensions"). A WE
adversary is a distinguisher; through LMP it is a prover whose message is **one bit**. There is
nothing to open. The analysis consumes exactly the proof content that laconicity removes.

**The refutation-indexed hybrid and its crux.** Read hybrid `H_i` as "every assignment that
falsifies one of the lines `C_1, …, C_i` of the refutation is killed (cannot decrypt)". `H_0` is
the real scheme (the axioms are the gate constraints), and the empty clause at the end kills
everything. The witness-indexed hybrid of `pq-we-hybrid-count-barrier` is the special case of
the tree-like resolution refutation by full case split (`2^{128}` leaves). But in each hop the
newly killed set (assignments falsifying a resolvent) was *already* killed (they falsify a
premise). So each hop changes the representation of a function and not its behaviour, which is
the function-hiding requirement of `pq-we-function-hiding-crux` again. (Jain–Jin's iO via proofs
of equivalence pays for each such hop with iO.) Short refutations only shorten the walk.

**Concrete verdict.** In `Def_WE_CircuitSAT` security is required for *every* unsatisfiable `φ`.
Every one has a refutation of length `≤ 2^{128}·poly` (the truth table), and `hardAt_chain`
already makes `2^{128}` hops affordable (about `2·128` bits of loss). The hop count is therefore
not the binding constraint; the per-hop crux is. **Route (3) gives no concrete gain.** Open target:

> **(P3)** A WE scheme and a proof of security for `Π_s` with `poly(s)` hops, each from a
> statement-independent assumption plus one local inference step of the refutation, where every
> hop changes only ciphertext data (no key whose function changes). Even for resolution this
> would be new, and it would survive every barrier recorded so far.

## 4. Batch ideas: splitting the 128-bit witness

### 4.1 Why BARG-style compression points the wrong way

Split `w = (w_1, w_2)`. Then `φ ∈ L ⇔ ∨_{w_1} [φ(w_1, ·) ∈ SAT]`, an **OR** of `2^{|w_1|}`
sub-statements. BARGs (and somewhere-extractable hashing) compress **ANDs**: their soundness
locates *one* false sub-statement and extracts there. In WE the AND is on the security side
(`∀w, φ(w) = 0`), and a distinguisher's advantage does not localize to one position the way a
cheating prover's false claim does. A guessing reduction ("pick the position `i*`") loses a
factor `2^{128}` in advantage, which in the `cost/adv²` accounting is the same `2·128` bits as the
`2^{128}`-hop chain of `hardAt_chain`. It does not remove the per-hop crux either. A succinct
OR-combiner for WE of sub-statements that are trivial (checkable in polynomial time) would itself
be WE for NP, since one can take one sub-statement per witness.

### 4.2 The compliant construction: BJKPW XWE (`γ = 1/2`)

BJKPW §1: with a private-key, unbounded-collusion key-policy ABE, Enc(`φ`, `b`) samples
`msk`, outputs keys `sk_{f_{w_1}}` for all `w_1 ∈ {0,1}^{m/2}` with
`f_{w_1}(w_2) = φ(w_1 w_2)`, and ciphertexts `ct_{w_2} = ABE.Enc(msk, w_2, b)` for all `w_2`.
The decryptor with `w = w_1 w_2` uses one key and one ciphertext. On a false `φ` every
(key, attribute) pair is unauthorized, and ABE security (their Definition 2.1, many keys and many
ciphertexts) hides `b`. With BGG+ (keys of size `poly(d, λ)`, key generation `|f|·poly(λ, d)`)
this is XWE with encryption time `2^{m/2}·poly` from **sub-exponential LWE**. That is
post-quantum, falsifiable, statement-independent, standard model, with no setup (the encryptor
holds `msk`).

Consistency with the barriers: the proof is a hybrid over the `2^{m/2}` ciphertexts. Each hop is
the selective single-challenge BGG+ reduction, which uses the *local* fact `φ(·, w_2*) ≡ 0` (a
partial truth table of `2^{m/2}` entries) and simulates all keys. Neither the hop count nor the
reduction time is polynomial, so `pq-we-hybrid-count-barrier` does not apply. The construction
never needs a key whose function changes, so it does not meet the function-hiding crux; it pays
for that with `2^{m/2}` explicit objects. The accounting is `hardAt_chain` with `T = 2^{m - a}`
ciphertext hops: `2^k·gain ≤ 2^{2(m - a)}·cost`, with `k` the per-hop strength **including the
reduction's simulation time** (about the encryption time).

Below `γ = 1/2`: BJKPW note that a `k`-input ABE gives `γ = 1/(k + 1)`, and that `γ = 1/3` would
already be significant progress. The only 2-input ABE (AYY, from LWE and pairings) is proved in the bilinear GGM, uses a
KOALA-type knowledge assumption, or is heuristic from lattices (excluded). Decryptor-chosen
attributes, the natural single-ciphertext shortcut, are the dead end of
`pq-we-decryptor-attribute-dead-end`.

### 4.3 Concrete cost for `Def_WE_CircuitSAT` (rough; word operations, RAM)

Unbalanced split: keys for `w_1 ∈ {0,1}^a`, ciphertexts for `w_2 ∈ {0,1}^{128 - a}`. Encryption
time is `2^a·K + 2^{128 - a}·C`. The dominant cost is BGG+ noise growth over the circuit depth
`d`: `log q ≈ d·log₂(growth per NAND)`. We use Ring-BGG+ with ring degree `n`, gadget length
`ℓ ≈ log q`, heuristic growth about `2√(ℓn)` per gate, and `n ≈ 118·log q` for about 410-bit
Ring-LWE strength. That strength is what the ciphertext hybrid needs:
`128 + 2(128 - a) + log₂(simulation time)`. Then:

* `K` (one key) ≈ `2^{12}` gates × `ℓ²` ring products, plus a preimage;
  `C` (one ciphertext) ≈ `(128 - a)·ℓ` ring elements.
* `d = 4096`: `log q ≈ 2^{16.4}`, `n ≈ 2^{23.3}`, `K ≈ 2^{83}`, `C ≈ 2^{56}`, best `a ≈ 50`,
  **total ≈ 2^{134.5}**, against brute force `2^{128}·2^{12} = 2^{140}` gate evaluations. The
  difference is within the error of the estimate.
* `d = 256`: `log q ≈ 2^{12.3}`, `n ≈ 2^{19.2}`, `K ≈ 2^{66}`, `C ≈ 2^{44}`, `a ≈ 53`,
  **total ≈ 2^{119}**, about `2^{21}` below brute force.

Decryption costs one EvalCT, well below these totals. These numbers are order-of-magnitude
estimates. On the Turing-machine cost model of `Def_WE` both sides pick up overheads
(`we-circuitsat-bruteforce-explicit-cost`: `2^{188}`, with routes to `2^{165}`), and they have not
been compared there.

### 4.4 Next steps on the lead

1. Register sub-exponential (Ring-)LWE at the needed strength, if it is not already registered,
   reproducing the source's distributions exactly.
2. State as theorem nodes: (i) BGG+ selective security as used (one challenge attribute, keys for
   every `f` with `f(x*) = 0`); (ii) the ciphertext hybrid via `hardAt_chain`; (iii) the
   combinatorial correctness and security of the split (`φ(w_1 w_2) = 1` gives an authorized pair;
   unsatisfiable `φ` makes every pair unauthorized).
3. Reduce depth before encryption: the key functions `f_{w_1}` are `φ` with `w_1` substituted, so
   constant propagation and depth-optimal re-synthesis help directly, since `log q` scales with
   `d`. Any trick that keeps BGG+ noise polynomial in the circuit *size* would make the route
   concretely strong; none is known for general circuits.

## 5. Setup

`Def_WE_CircuitSAT` has no trusted setup, so any CRS is produced by `Enc`. That is harmless:

* The encryptor is honest and its coins stay hidden, so designated-verifier secrets and setup
  trapdoors (GHKKP's `td`, a BGG+ `msk`) stay secret.
* A fresh CRS per ciphertext against an adversary fixed after `φ` needs only **static**
  soundness. This is the regime Gentry–Wichs leave open (`pq-we-reduction-query-flattening` §2).
* The cost is a ciphertext that carries the CRS or keys. That counts in `time(Enc)`, which is
  what §4.3 accounts for.

Setup is therefore not where any route fails. Routes (1)/(1') fail at extraction, (2) is the
target itself, (3) fails at the function-hiding crux, and (4) works with exponential (but
non-trivial) cost.

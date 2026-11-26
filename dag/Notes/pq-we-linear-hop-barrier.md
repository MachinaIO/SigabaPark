---
title: Linear-embedding hops in data-only witness-indexed WE hybrids - where the observation fails, and the barriers it does give (kill accounting)
refs: [definition:WE_CircuitSAT, note:pq-we-non-lattice-algebras, note:pq-we-affine-syzygy-barrier, note:pq-we-hybrid-count-barrier, note:pq-we-gap-structure-routes, note:pq-we-evaluation-oracle-crux, theorem:AdvancedEncryption.WE.LinearHop.card_strict_steps_le_finrank, theorem:AdvancedEncryption.WE.LinearHop.hop_dichotomy, theorem:AdvancedEncryption.WE.LinearHop.card_killed_le_finrank, theorem:AdvancedEncryption.WE.Codes.card_fresh_le_finrank, theorem:AdvancedEncryption.WE.Syzygy.exists_affine_syzygy]
tags: [witness-encryption, barrier, strategy]
---
Design-AI sub-task on `Def_WE_CircuitSAT`: turn the "linear-reduction observation" of
`pq-we-non-lattice-algebras` (§2b) into a precise barrier, or find where it fails. Summary:

* **As stated, the observation cannot be completed.** It constrains the hops that a reduction
  justifies. A planted witness never stops decrypting at such a hop. It stops at the hop indexed by
  itself, which no reduction justifies (§1).
* **The useful object is the coupled walk, not the reduction.** Couple all hybrids in one
  probability space (the key `PK` is the same throughout), look at the ciphertext shifts the hops
  make, and count. This gives three barriers. Barrier 0 holds for every data-only walk. Barrier A
  is complete and holds at every noise rate: no succinct scheme can have a walk whose hops all
  re-randomize uniformly along subspaces, which is the shape linear LWE/LPN reductions produce.
  Barrier B, for hops that add independent noise of any law (smudging, Bernoulli flooding),
  bounds the number of killed witnesses by the ciphertext's bit length, under an extra
  statistical hypothesis (§2–§4).
* **On the other side of the boundary** (§5–§6) are walks whose hops are not additive and
  independent: overwriting, secret-correlated or rounding hops, and decryption functionals that
  depend on ciphertext data (`G^{-1}`, FHE-hidden attributes). The natural candidate there,
  positional predicate encryption, is sketched in §6. It reaches the known open cruxes (strong
  attribute hiding; keyless target cancellation) and does not escape them.

What is proved in Lean (complete proofs, Mathlib only):
`AdvancedEncryption.WE.LinearHop.card_strict_steps_le_finrank` (a monotone chain of subspaces has
at most `dim` strict steps), `AdvancedEncryption.WE.LinearHop.hop_dichotomy` (a functional either
ignores a linearly embedded challenge or sees it uniformly), and
`AdvancedEncryption.WE.LinearHop.card_killed_le_finrank` (per-hop kill count). Everything else is
an informal argument, checked step by step by the submitting agent: the planted-statement steps,
the probability bookkeeping, and the entropy accounting of Barrier B.

## 0. Model

Statement `φ`, witness space `{0,1}^n` in lexicographic order, hybrids `H_0 = Enc(φ, m), …,
H_{2^n}`. Each hybrid outputs `(PK, CT)`. The model has four parts:

* **Data-only.** The law of `PK` does not depend on the hybrid index or on `m`. So all hybrids can
  be coupled with **one** `PK`: sample `PK`, then the sequence `CT_0, CT_1, …` with each `CT_j`
  distributed as in `H_j` given `PK`. Any coupling is allowed, e.g. the one a proof's reductions
  suggest. Write `x_j = CT_{j+1} − CT_j` for the **shift** of hop `j`.
* **Linear decryption.** `CT ∈ F^N` for a finite field `F` (`F_q`, `F_2`), and the decryptor's
  output at witness `w` is `g(PK, φ, w, h(CT))`, where `h = h_{PK,φ,w}` is linear (a scalar
  functional in Barrier A, any linear map `F^N → F^d` in Barriers 0 and B) and `g` is arbitrary
  (rounding, majority, anything). BGG+-, GSW- and decomposed-LWE decryptions whose evaluation
  matrices depend only on `PK`, `φ`, `w` have this form. The bit length of `CT` is `N log₂ q`.
* **Local hops.** If `φ(w) = 0` then `H_w ≈ H_{w+1}`, and `H_{2^n}` hides `m`.
* **Messages.** `m ∈ {0,1}`, uniform. "Correct" means that the decryptor outputs `m`.

**Planted statements.** As in `pq-we-affine-syzygy-barrier`: `K` planted witnesses
`w^{(t)} = (t − 1, x_t)`, `y_t = Prg(x_t)`, `φ_real(t, x) = [Prg(x) = y_t]`. Let `j_t` be the index
of `w^{(t)}`. Then:

* **(L) live before its own hop.** In `H_{j_t}(φ_real)` the decryption at `w^{(t)}` is correct
  with probability `≥ 1 − δ` for each `m`. Replace `y_1..y_{t−1}` by random strings; the walk
  `H_0 → H_{j_t}` then only crosses non-witnesses. The PRG step is valid: the test and the sampler
  of `H_{j_t}` use `x_t` but no `x_s` with `s < t`.
* **(D) dead after its own hop.** In `H_{j_t+1}(φ_real)`,
  `Pr[correct | m=0] + Pr[correct | m=1] ≤ 1 + ε`. Replace `y_{t+1..K}` by random strings and walk
  forward to `H_{2^n}`.

Here `δ` collects the correctness error, the hop advantages before `j_t` and the PRG advantages,
and `ε` the advantages after `j_t`. In the `2^n`-hop accounting of `pq-we-hybrid-count-barrier`,
both are small when the premises are sized for it. `φ_real` has size about `K(|Prg| + log K)`.

**Erratum for `pq-we-affine-syzygy-barrier`.** Its live side samples `H_{w*}` with
`w* = w^{(r)} + 1`, which needs `x_r`, while replacing `y_r` by a random string through the PRG.
That PRG step is invalid as written. Take `w* = (r, 0…0)`, the first index of the next block,
instead. The live side then needs no `x_s` with `s ≤ r`. The dead side walks forward from `w*`.
The rest of that argument is unchanged.

## 1. Why the linear-reduction observation alone gives nothing

Fix the hop at a **non-witness** index `j` and an efficient test that decrypts at a witness
`w^{(t)}`. Any valid hop preserves that test up to the hop advantage, whether or not it is linear,
because the decryptor is an efficient distinguisher. So no planted witness ever switches from
live to dead at a valid hop. By (L) and (D), `w^{(t)}` switches exactly at **its own** hop
`j_t → j_t + 1`, where `φ_real(w^{(t)}) = 1` and no reduction exists.

Planting cannot reach that hop either. Every object at index `j_t` is sampled with `x_t`, so the
statement can only be switched to "`w^{(t)}` is a non-witness" by a PRG step on `y_t` that the
sampler itself breaks. The hybrid at a witness index may even evaluate `φ` at its own index and
behave differently. The observation of §2b of `pq-we-non-lattice-algebras` (a linear reduction's
embedding `L` is annihilated by every later live functional) is true, but it concerns the wrong
hops. A barrier must constrain the **witness-index hops**. The rest of this note does so through
the coupled walk.

## 2. Barrier 0: every data-only walk needs tolerated perturbations (fully general)

**Counting lemma** (`card_strict_steps_le_finrank`, proved). A monotone chain of subspaces of `F^N`
has at most `N` strict steps.

For one realization of the coupled walk, let `R_j = span{x_i : i < j}`, a monotone chain. For a
planted `t`, with `h_t = h_{PK,φ_real,w^{(t)}}`, define two events:

* `A_t` (untouched before): `R_{j_t} ⊆ ker h_t`, i.e. no earlier shift moved `h_t(CT)`;
* `B_t` (touched by its own hop): `x_{j_t} ∉ ker h_t`.

On `A_t ∧ B_t`, `x_{j_t} ∉ R_{j_t}`, so `R` steps strictly at `j_t`. Distinct `t` have distinct
`j_t`, so `#{t : A_t ∧ B_t} ≤ N` for **every** realization. On `¬B_t`, `h_t(CT_{j_t+1}) =
h_t(CT_{j_t})` and the two outputs agree. So by (L) and (D),
`Pr[B_t] ≥ (1 − ε)/2 − δ` (average over `m`). Hence:

> **Barrier 0.** For every coupling of a data-only walk with linear decryption over a field,
> `Σ_t Pr[¬A_t ∧ B_t] ≥ K((1 − ε)/2 − δ) − N`. With `K ≫ N`, almost every planted witness has
> its decryption value **moved by an earlier hop and still correct** at its own hop (by (L)).

So a succinct scheme (`N ≪ K`, i.e. ciphertext length `≪ |φ| / |Prg|`) must tolerate
perturbations of live decryption values. The kill at its own hop must then be a perturbation of a
different *kind* or *size*. This is the "noise escape" of `pq-we-non-lattice-algebras`, shown to
be **necessary**. Barrier 0 needs no reduction, no noise model and no hypothesis on the
witness-index hops. Barriers A and B exclude the two natural kinds of perturbation.

## 3. Barrier A: uniform re-randomization hops (complete, any noise rate)

**Hypothesis (URR walk).** The walk has a coupling `CT_{j+1} = CT_j + s_j` in which `s_j` is
uniform on a subspace `S_j` given the past (`PK`, `m`, `CT_0`, `s_{<j}`, `S_{≤j}`). The law of
`(PK, S_0, S_1, …)` does not depend on `m`. The **witness-index hops are included**. Decryption is
a scalar functional `h_t` followed by any `g`.

**Where linear reductions enter.** A hop proven by a reduction that embeds its challenge `b`
affinely, `CT = L b + C` with `(PK, L, C)` independent of `b`, has the uniform branch
`L u + C ~ (L b + C) + L u'` for a fresh uniform `u'`. Between the simulated distributions it is
therefore a URR step with `S = range(L)`. This holds for LWE `(A, sA + e)` and LPN alike, where
`L` and `C` may depend on the public `A`. The hypothesis asks that the witness-index hops, which
no reduction covers, have the same form. That is the case in "uniform-replacement" positional
designs, where `H_{w+1}` is defined from `H_w` by replacing the component of index `w` by uniform
regardless of `φ(w)`.

**Proof.** By `hop_dichotomy` (proved), a step with `S_j ⊄ ker h_t` adds to `h_t(CT)` a value that
is uniform given the past. Every later step adds either `0` or a fresh uniform value, so
`h_t(CT)` stays uniform given `(PK, m)`. With the law of `(PK, ¬A_t)` independent of `m`, we get
`Σ_m Pr[correct ∧ ¬A_t | m] ≤ Pr[¬A_t]`, and (L) gives `Pr[¬A_t] ≤ 2δ`. With §2:

> **Barrier A.** `K((1 − ε)/2 − 3δ) ≤ N`. A succinct scheme (`N < K((1−ε)/2 − 3δ)`, roughly
> `N < |φ| / (2|Prg|)`) cannot be proven secure by a walk of URR hops, whatever the noise rate,
> modulus or decoder `g`, for any per-decryption error `δ < 1/6`.

This closes the LPN constant-noise escape (§2b of `pq-we-non-lattice-algebras`) for all
linear-embedding proofs, including when the witness-index hops are of the same kind. Over `Z_q`
with composite `q`, a uniform element of a submodule is uniform only on a subgroup of `Z_q`, so a
"touch" can be partial. Barrier B covers that case.

**Per-hop variant** (when only the witness-index hops are known to be URR, with valid hops
arbitrary, so that no common coupling exists). Pick a random planted `r`. The hop at `w^{(r)}`
must touch `h_r` and spare `h_t` for `t > r`. Use (L) for `t > r` at index `j_r + 1`, obtained by
walking back from `(r, 0…0)` over non-witnesses. By `card_killed_le_finrank` (proved), at most `N`
indices can have such a hop with *all* later functionals untouched. So
`(1 − ε)/2 − δ ≤ N/K + 2Kδ`. This is a contradiction when `δ ≤ 1/(16K)` (negligible-error
lattice decryption), but not for constant-error LPN decryption. The chain in Barrier A is what
removes the union bound.

## 4. Barrier B: independent additive noise of any law (informal, entropy accounting)

**Hypothesis.** `CT_{j+1} = CT_j + X_j` with `X_j` independent of `(CT_0, m, X_{<j})` given `PK`.
The law of `X_j` may be anything: Gaussian smudging, Bernoulli flooding, uniform, or a constant
shift. `CT` lives in any finite abelian group of bit length `N log₂ q`, and `h_t` is any
homomorphism, possibly vector-valued, followed by any `g`. Instead of (D), assume **(D_stat)**:
`E_PK TV(h_t(CT_{j_t+1}) | PK, m=0 ; … | m=1) ≤ ε'`.

**Argument.** Let `Y_j = Σ_{i<j} X_i`. Each hop adds independent noise, so `H(Y_j | PK)` never
decreases. At `j = j_t`, with `a = h_t(Y_j)` and `b = h_t(X_j)` (independent):
`H(Y_{j+1}|PK) − H(Y_j|PK) = I(Y_j + X_j ; X_j | PK) ≥ I(a + b ; b | PK)` (data processing).
If this is small, then by Pinsker `a + b` is close in law to `a + b₀` for a typical constant
`b₀`. Then `h_t(CT_{j_t+1})` is close to a bijective shift of `h_t(CT_{j_t})`, whose TV between
`m = 0, 1` is `≥ 1 − 2δ` by (L). This gives `I ≥ (1 − 2δ − ε')² / (2 ln 2)` bits per kill, and
`H(Y | PK) ≤ N log₂ q`:

> **Barrier B.** `K (1 − 2δ − ε')² / (2 ln 2) ≤ N log₂ q`. **Each killed witness costs a constant
> number of bits of ciphertext entropy.**

This covers smudging over `Z_q` at any modulus-to-noise ratio, so it covers escape 4 of
`pq-we-affine-syzygy-barrier` as long as the hops are additive and independent, and it covers
Bernoulli flooding for LPN. Its weak point is (D_stat). Hiding is computational, and statistical
deadness of the single value `h_t(CT)` given `PK` follows only if the best test on it, which may
depend on `PK` (for example the sign of a `PK`-dependent bias over `F_2`), is efficient. Barrier A
does not need (D_stat).

## 5. The boundary, hypothesis by hypothesis

What a construction on the other side of each hypothesis looks like:

| Hypothesis | Violating shape | Status |
| --- | --- | --- |
| data-only (fixed `PK`) | keys change along the walk | the function-hiding route, `pq-we-function-hiding-crux` |
| linear decryption | functional depends on ciphertext data: `G^{-1}` of ciphertext parts (GSW products), products of ciphertext matrices (GGH15 data chains), rounding of intermediate values, degree-`D` tensors | open; escapes 1–2 of `pq-we-affine-syzygy-barrier`; GGH15 chains face backward kernel propagation |
| additive, independent hops (A, B) | (i) **overwrite** hops `CT ↦ P·CT + fresh` (replace a block by a fresh non-uniform encryption); (ii) **secret-correlated** shifts (changing an attribute in BGG+ encodings shifts by `sᵀ(Δx ⊗ G)`); (iii) **rounding** embeddings `⌊L b + C⌉_p` (LWR), where the change depends on `C`; (iv) `G^{-1}(b)` embeddings; (v) directions or noise chosen from `CT` or `m` | Barrier 0 still applies to all of them: earlier hops must perturb live values without killing them |
| uniform touch (A only) | non-uniform perturbations | Barrier B if independent; syzygy barrier if bounded-norm with `q/B_err > 4M` |
| succinctness `N log q ≪ K` | ciphertext linear in `|φ|` (BGG+ with the statement as attribute) | not covered by any of these barriers |

Two remarks on the table:

* (ii) is often not a real escape. For uniform `s`, `sᵀD h_t` is uniform unless `D h_t = 0`, so
  touching a functional destroys it as in Barrier A. Example: a plain BGG+ "position attribute"
  `p` with a fixed decryption functional. The value `sᵀ(B − p ⊗ G)h_w` is affine in the bits of
  `p`. It must be constant on `{p ≤ w}`, whose affine span contains every low bit, and can change
  at `p = w + 1` only when `w + 1` is a power of two. So at most `n` witnesses can be killed, as
  §2 predicts.
* (iii) and smudging are the same phenomenon: perturbations whose size depends on `‖h‖`. In the
  bounded-norm regime, the affine `{−1,0,1}` syzygy (`exists_affine_syzygy`) bounds the
  perturbation of `h_r` by `(M−1)` times that of the live ones. So the escape needs modulus-to-noise
  ratio `≲ 4M` **and** a non-additive or non-independent hop, since Barrier B excludes the
  additive independent case.

## 6. A construction on the other side: positional predicate encryption (sketch and analysis)

The cleanest shape that violates "linear decryption" and "additive independent hops" at once is
predicate encryption with the **position as a hidden attribute**:

* `CT` = `FHE.Enc(p)` (honest `p = 0`), BGG+ encodings `sᵀ(B_i − c_i G) + e_i` of the bits `c_i`
  of the FHE ciphertext and of the FHE secret key (GVW-style), and `sᵀu + e + m⌊q/2⌉`.
* The decryptor with `w` evaluates `f_w(p) = φ(w) ∧ [w ≥ p]` under FHE and BGG+, then the FHE
  decryption, whose final step is linear. The evaluation matrix depends on the FHE ciphertext bits,
  so **decryption is not a fixed functional of `CT`**, and Barriers 0, A and B do not apply.
* The hop `p → p + 1` at a non-witness `p` is FHE semantic security plus attribute hiding. The
  outputs of all `f_w` agree on `p` and `p + 1` when `φ(p) = 0`.

Analysis:

1. **The hop needs strong attribute hiding.** Witnesses `w > p + 1` decrypt in both hybrids, so `p`
   must stay hidden from holders of *decrypting* keys. LWE predicate encryption gives only weak
   attribute hiding (keys that do not decrypt). Strong attribute hiding for circuit predicates is
   not known from LWE. With decrypting keys, the attribute leaks through the evaluation path.
2. **There are no keys in WE.** The decryptor must cancel `sᵀ B_{f_w}` without a trapdoor, for each
   of `2^n` predicates `f_w`. That is the witness-oblivious target-cancellation crux of
   `pq-we-hybrid-count-barrier`, i.e. the second representation of `pq-we-evaluation-oracle-crux`.
3. **Kills.** At a witness `p = w^{(t)}`, the hop must change only `f_{w^{(t)}}`'s output. In
   this design that holds by the semantics of `f_w`, not by a perturbation, which is why the
   design is outside the barriers. But it needs both 1 and 2.

So the construction is genuinely on the other side, and all its difficulty lands on the two known
cruxes. A version with a public attribute and linear decryption falls back under §5(ii). No other
candidate found here crosses the boundary more cheaply. The rounding (LWR) and overwrite variants
of uniform-replacement designs remain unanalysed beyond Barrier 0 and the syzygy bound. They are
the natural next targets: a walk in which each hop overwrites one block of a succinct ciphertext
with a fresh **non-uniform** encryption, so that Barrier 0's tolerated perturbations come from the
overwrite while entropy does not accumulate.

## What it implies

A data-only, statement-independent proof for a succinct scheme with linear decryption cannot
consist of linear-embedding hops: Barrier A is complete for them at every noise rate. It also
cannot consist of hops that add independent noise: Barrier B, under (D_stat). The challenge must
enter **non-linearly** (rounding, `G^{-1}`, overwriting with fresh non-uniform encryptions), or
the decryption functional must depend on ciphertext data, or the keys must change. And every
data-only proof must, by Barrier 0, have earlier hops perturb live decryption values that then
survive.

---
title: WE from LWE with trapdoor hints (AJLW26) - the error-encoded witness PRF, the public trapdoor as a linear zero test, and the evaluation-oracle crux
refs: [definition:WE, definition:WE_CircuitSAT, note:pq-we-evaluation-oracle-crux, note:pq-we-witness-prf-masked-evaluator, note:pq-we-masked-evaluator-mechanisms, note:pq-we-hybrid-count-barrier, note:pq-we-matrix-collision-barrier, note:pq-we-affine-syzygy-barrier, note:pq-we-tree-encodings, note:pq-we-function-hiding-crux, theorem:AdvancedEncryption.WE.Tree.fixed_offset_attack, theorem:AdvancedEncryption.WE.MaskedEval.mask_leak]
tags: [witness-encryption, strategy, barrier, attack]
---
Design-AI sub-task (z) on `Def_WE_CircuitSAT`. The human's idea: use **LWE with trapdoor hints**
(TLWE) and the **threshold difference revealing encryption** (TDRE) of Aggarwal, Jain, Lin and Wu,
"On the Hardness of LWE with Trapdoor Hints and Applications to Fuzzy Cryptography" (ePrint
2026/2927, "AJLW26"). Encode a constrained-PRF output in the LWE **error**, so that the
master-side and the constrained-key-side evaluations at `(x, w)` are close exactly when
`C(x, w) = 1`. A public trapdoor then removes the `sᵀA` mask only for valid pairs and releases a
witness-independent payload, which gives a witness PRF and hence WE.

The six theorem nodes named in this note (`AdvancedEncryption.WE.TLWE.*`) come with complete
proofs in the same PR. They are not listed in `refs` because they are not merged yet.

## Summary

1. **What TLWE gives (§1).** A full public trapdoor `T` of a fixed matrix `A` can be published
   next to `sᵀA + e`, provided the error is wide (`σ_e ≥ (q/τ)·ω(√log n)`) and the trapdoor is
   long (`‖T‖ ≈ mτ`). In AJLW26's public-coin form, `A = [B | BR + G_τ]` and the trapdoor is `R`
   itself. The result is a **norm hierarchy**. Operations of norm much smaller than `τ` (BGG+
   evaluation, short combinations) keep errors below `q`. Trapdoor operations (norm at least `τ`)
   push every wide error past `q`. So the trapdoor decodes **only vectors whose wide error parts
   cancelled exactly**.
2. **Normal form (§2).** Every vector the decryptor computes is `ct·L` for a public matrix `L`.
   For two evaluations on one key, the error difference after evaluation is a fixed public linear
   image of the input error difference (`eval_difference`; TDRE's own identity is `tdre_cancel`).
   The trapdoor decodes `ct·L` only if the secret part has the form `(·)·A` and the error `E·L` is
   short. The set of such `L` is closed under short combinations (`linear_closure`). So
   **the public trapdoor acts as a linear zero test on the hidden error.** Decoding has two-sided
   correctness (`unique_decoding`).
3. **Dichotomy for the human's construction (§3).**
   * *Case I.* The decoded matrix depends on `w` (for example `A_{U_w}`). Then a trapdoor for
     `A_{U_w}` is needed for every `w`. No public object yields one at valid `w` without also
     yielding one at invalid `w`. This is the evaluation-oracle crux and its matrix-collision
     barrier again.
   * *Case II.* The decoded matrix is fixed. Then validity must sit entirely in the hidden error:
     "`E·L_w` is short iff `C(x, w) = 1`". The error must be planted with `φ`-dependent structure.
     We give the canonical way to do this (error-level BGG+) and show that it either falls back to
     Case I or yields a linear zero test. Linear zero tests are broken by shortcut and
     linearization attacks, and the fixed offset reappears at the error level
     (`invalid_offset_cancel`).
4. **TLWE cannot be the hop that carries security (§4).** Under the exact TLWE distribution
   (Gaussian error independent of the public data), no short public functional of the error is
   below the decoding radius. Correctness needs one at every witness. So the real ciphertext is
   never a TLWE instance, and the step "structured error ≈ Gaussian error" is the entire WE
   security. By `pq-we-hybrid-count-barrier` this step must be statement-dependent or take about
   `2^128` witness-indexed hops. Linear zero-test designs cannot host such hops: an antitone chain
   of subspaces changes at most `dim` times (`antitone_chain_few_changes`).
5. **Verdict.** The idea does not escape the evaluation-oracle crux. The "master evaluation" side
   is the crux object under a new name (§3, Case I). If it is moved into the error (Case II), it
   becomes a GGH13-style zero test on a hidden error lattice, which needs non-falsifiable or
   statement-dependent assumptions. What remains open, stated precisely in §6, is a hidden-matrix
   (GGH15-type) variant in which TLWE replaces the small-norm zero test. That is the masked
   γ⊗-GGH15 line of `pq-we-witness-prf-masked-evaluator`, and the same missing lemma remains.

## 1. What AJLW26 proves (reproduced from the paper)

* **Definition 1.1 (TLWE).** Distinguish `(A, T, sᵀA + eᵀ mod q)` from `(A, T, uᵀ)` for
  `A ← Z_q^{n×m}`, `e ← D_{Z^m, σ_e}`, with `T` a Gaussian full trapdoor of `Λ_q^⊥(A)` of width
  `σ_t`.
* **Theorem 1.1 (informal).** For `4n log q ≤ m ≤ poly(n)`, `τ^c/2 < q < τ^c`,
  `σ_t ≥ m·τ·ω(√log n)` and `σ_e ≥ (q/τ)·ω(√log n)`, TLWE is hard assuming LWE in dimension
  `Ω(n/log q)` with modulus-to-noise ratio `τ m^{1.5}`. Below `σ_e·σ_t = o(q/√m)` it is trivially
  broken: `eᵀT mod q = eᵀT` over `Z`.
* **Theorem 4.1 (public-coin form, secret reuse).** For `(A, R) ← TdSamp`, i.e.
  `A = [B | BR + G_τ]` with `R` a random binary matrix:
  `(A, R, sᵀA + eᵀ, C, sᵀC + e'ᵀ) ≈_c (A, R, uᵀ, C, u'ᵀ)`, with `σ ≥ τ^{c−1}·ω(√log λ)` on `e` and
  `e'` of width `σ' ≥ γ√(m'+l)·ω(√log λ)`. The extra samples on `C` carry payloads.
* **Theorem 4.2 (error leakage).** Hardness survives a leakage `h(e)` of `O(log λ)` bits, for
  Gaussian homogeneous trapdoors `T` only. Whether it holds for the public-coin `R` is left open
  in the paper.
* **TDRE (Construction 6.1).** Public key `(A, T, C)`. `Enc(x, y) = (sᵀA + xᵀ, sᵀC + eᵀ + ⌊q/2⌋y)`,
  with the message `x` **as the LWE error**. `Rev` runs `TdInvert` on `b1 − b2 = (s1 − s2)ᵀA + (x1 − x2)`:
  it returns `(s1 − s2, x1 − x2)` if `‖x1 − x2‖ ≤ t` (with `t ≪ q/(4m²τ·ω(√log m))`), and `⊥`
  otherwise. The `⊥` side uses `λ1(L_q(Aᵀ)) = q` (Lemma 3.2) and `‖x_i‖ ≤ B < (q − t)/2`.
  `tdre_cancel` is the identity, and `unique_decoding` is the farness half in a general form
  (a lattice with all nonzero vectors of some coordinate `≥ B`).

**The decisive quantitative fact.** The decoding radius `t ≈ q/(4m²τ)` is at least a factor
`4m²·ω(√log)` below the TLWE error width `q/τ`. So a decodable vector cannot be a "smallish"
combination of wide errors. **Its wide components must cancel exactly**, and only
small-norm terms (input noise of norm much smaller than `q/(m²τ)` times evaluation growth) may
survive.

## 2. The linear normal form of every decryptor

Collect all LWE-type components of a ciphertext into one row `ct = t·M + E`: secret `t`, public
`M`, hidden error `E`. Rounding is the only non-linear public operation besides decoding, and
`pq-we-masked-evaluator-mechanisms` shows that it only adds deterministic errors. So every vector
the decryptor obtains before decoding is `ct·L` for a public `L` computed from `(φ, w)` and the
public data.

* **Two evaluations on one key** (`eval_difference`). If `c1_i = s1(A_i − x_i G) + e1_i` and
  `c2_i = s2(A_i − x_i G) + e2_i`, then
  `EvalCt(f, c1) − EvalCt(f, c2) = (s1 − s2)(A_f − f(x)G) + evalErr(e1 − e2, f)`.
  The error difference evolves by a **public linear map that does not depend on `f(x)` being 0
  or 1**, beyond the intermediate values `a(x)` that appear in `evalErr`'s recursion. So
  "close iff valid" cannot come from the evaluation mechanics. It must be planted in
  `e1 − e2`.
* **Decoding condition.** A public trapdoor of a fixed `A` decodes `ct·L` iff (i) `M·L = Q·A`
  for some `Q` (secret part in `A`-form; it then returns `t·Q`) and (ii) `E·L` is within the
  radius. By `unique_decoding`, the output is the true `(tQ, E L)` or `⊥`.
* **Linear closure** (`linear_closure`). If `L1, L2` satisfy (i), so does `a·L1 + b·L2`, with
  secret part `t(aQ1 + bQ2)` and error `E(aL1 + bL2)`. For short `a, b` the error stays within
  a constant factor. **The passing set is a lattice up to norm bounds, i.e. a linear zero test on
  `E`.** This is the TLWE instance of the noisy-linear decryption covered by
  `pq-we-affine-syzygy-barrier`.

## 3. The human's construction, worked out

### 3.1 The natural instantiation (TDRE plus BGG+)

The ciphertext holds two BGG+ encodings on public matrices `A_1..A_L` with a TLWE-type public
trapdoor. The master side has secret `s1` and an attribute `φ_0` with `U_w(φ_0) = 0` for all `w`.
The constrained side has secret `s2` and attribute `φ` (BV15 convention flipped: value `0` on
valid pairs). There is a payload sample `s1ᵀC + e' + ⌊q/2⌋μ`. At `w` the decryptor computes
`EvalCt(U_w, c1) − EvalCt(U_w, c2) = (s1 − s2)ᵀA_{U_w} + φ(w)·s2ᵀG + (e1 H_{w,φ_0} − e2 H_{w,φ})`.

* The two evaluation matrices `H_{w,φ_0}` and `H_{w,φ}` differ (they depend on the attribute).
  So even identical input errors do not cancel: `e(H_{w,φ_0} − H_{w,φ})` is wide whenever `e` is
  TLWE-wide.
* The decoded matrix is `A_{U_w}`, which depends on `w`.

### 3.2 Case I: decoded matrix depending on `w`

The decryptor needs a trapdoor of `A_{U_w}` (or of `[B | A_{U_w}]`) for every `w`, from public data.

* **Public-coin trick.** Take `A_i = B R_i + φ_{0,i} G` with public `R_i` (AJLW26 Theorem 4.1
  form, extended per input). By `sim_relation`, `A_f = B R_f + f(φ_0) G` with public
  `R_f = EvalSim`. So `[B | A_f]` has the public trapdoor `R_f` exactly when `f(φ_0) = 1`.
  This is a witness-dependent trapdoor **only if `φ_0 = φ`**. Then the decryptor holds a trapdoor
  at valid `w`, but the attribute is the statement and the encodings on `A_i` are
  `s(B R_i + φ_i G) + e_i`. With `b = sB + e_B` in the ciphertext,
  `c_i − b R_i = φ_i·sG + (e_i − e_B R_i)`. The wide errors protect this only if they do not
  cancel. Then the evaluated vectors are wide too, and decoding at valid `w` fails. If the errors
  are correlated so that they cancel, every input bit `φ_i = 1` already decodes `s`. Evaluation
  adds nothing: the errors evolve by public linear maps (§2).
* **General form.** A public procedure that outputs a trapdoor of `A_{U_w}` at valid `w` and not
  at invalid `w` is a witness-oblivious trapdoor-generating evaluator, i.e. the evaluation-oracle
  crux with "trapdoor of `A_{U_w}`" in place of "`sᵀA_{U_w}`". If the trapdoor is available at
  **all** `w` (public-coin with `φ_0` all-accepting), it is available at invalid `w` as well. The
  decoded value there is `(s1 − s2)` up to the gadget term, so validity does not gate decoding.
  As in `pq-we-evaluation-oracle-crux` (consequence 3, "`X` with a public trapdoor"), only the
  errors can then stop the attack, and that is Case II.

### 3.3 Case II: fixed decoded matrix, validity in the hidden error

Here `M·L_w = Q_w·A` for every `w`, and correctness requires `E·L_w` short iff `C(φ, w) = 1`.

**Column operations do not preserve the form.** With the public trapdoor, `A L = Q A` can be
solved for any `Q`. But a sampled solution has norm at least about `τ`, and so has every solution
of the form `I + T·Z`. Either way `E·L` is wide (`E T mod q = ct·T` is public and pseudorandom by
TLWE). For generic `A`, heuristically, the only solutions of norm much below `τ` are the scalar ones:
`{QA}` is an `n²`-dimensional subspace of the `nm`-dimensional space in which `AL` behaves like a
random point. So the
`w`-dependent processing must act on the **row** side: several samples `CT = S A + E` (`k` rows)
and short public combinations `α(w) ∈ Z^k`, giving `α(w)ᵀCT = (α(w)ᵀS)A + α(w)ᵀE`.

**Planting.** By §1, `α(w)ᵀE` short forces the wide part of `E` to cancel exactly. Write
`E = ΠᵀF + N` with `F` wide and `N` short. Then valid means `Π α(w) = 0` (a hidden kernel). The
release must be witness-independent: `α(w)ᵀS = σ` for all witnesses, e.g. `S = e_0 σ + ΠᵀZ`
with `α_0(w) = 1`. Then the decryptor obtains `σᵀA + α(w)ᵀN` and decodes `σ`.

**Attacks.**

* *Public-α shortcut.* If `α(w)` is a public function (necessary for shortness: Kilian-type
  randomization of a branching program destroys shortness), validity "`α(w) ∈ ker Π`" is
  membership of a public vector in a hidden lattice. For a permutation branching program,
  `α(w) = e_{state(w)}`, and correctness at true statements forces `e_acc ∈ ker Π`. The adversary
  decodes `σ` with `α = e_acc` and needs no witness. In general, any short `α ∈ ker Π` with
  `α_0 = 1` works.
* *Linearization.* Degree-2 Veronese `α(w̄) = (1, w̄, w̄ ⊗ w̄)` over the Tseitin-extended witness
  makes each NAND constraint `g = 1 − ab` a public linear functional `c_k`, and `Π = Cᵀ` gives
  correctness. But `Cα = 0, α_0 = 1` has short non-rank-one solutions (set the product coordinates
  freely to satisfy each constraint), so `σ` leaks on every statement. Higher-degree liftings
  (Sherali–Adams type) are at best a statement-dependent heuristic.
* *Error-level BGG+ with a fixed offset* (`invalid_offset_cancel`). The canonical way to make
  `E·L_w` small exactly when `f_w(φ) = 0` with column operations is to make the error an encoding:
  `E_i = ρ(Ω_i − φ_i G) + ν_i` with short `ρ`, short public `Ω`. Then
  `E·H_{f,φ} = ρΩ_f − f(φ)·ρG + ν_f`. It fails twice:
  1. The column operations `H_{f,φ}` also act on the secret part, giving `sᵀA H_{f,φ}`, which is
     back in Case I.
  2. Two invalid points have **the same offset** `ρG`, which cancels:
     `E(H_{f1} − H_{f2}) = ρ(Ω_{f1} − Ω_{f2}) + (ν_{f1} − ν_{f2})`, which is short. Differences of
     invalid evaluations pass the zero test. This is the error-level analogue of
     `AdvancedEncryption.WE.Tree.fixed_offset_attack` and of `mask_leak` (canonical deviation
     `sᵀG` there, `ρG` here). Without the `sᵀA` wrapper the blocks with `φ_i = 0` are
     `ρΩ_i + ν_i` over the integers, and least squares recovers `ρ`.
* *Point-dependent offsets.* BV15 avoids `mask_leak` by a nonlinear deviation (`sᵀD_x` after
  rounding). At the error level all deviations are public linear images `d·K_w` of one hidden
  vector `d` of polynomial dimension, so they satisfy short linear relations (dimension count).
  A rounding-based deviation `⌊sᵀA_w⌉` puts the PRF into a rounding error determined by the
  **secret** term `sᵀA_w`, i.e. it again needs the master value `sᵀA_{U_w}` (crux).

### 3.4 Is the master side new?

No. In Case I the master-side vector `s1ᵀA_{U_w} + e_master` is exactly the crux object
`F_{s,A}(w)` of `pq-we-evaluation-oracle-crux`, with a second secret. The trapdoor replaces the
requirement "the two secret parts cancel" by "the secret-part difference is decodable", which
needs a `w`-dependent trapdoor, and that is the same witness-oblivious problem. In Case II there is
no master side: the zero test on `E` plays its role, and it is a hidden-lattice zero test of
GGH13 type.

## 4. Security, statement independence and the hybrid-count barrier

* **TLWE instances are statement-independent** (`A, T` or `R`, one Gaussian error). By
  `pq-we-hybrid-count-barrier`, any proof with polynomially many hops, each either statistical on
  false `φ` or computational under TLWE/LWE, would put NP in SZK. TLWE changes nothing here.
* **Where the barrier bites.** Under the exact TLWE hypothesis, `α(w)ᵀE` for any short public
  `α` is a Gaussian of width at least `q/τ`, far above the radius, so nothing decodes. The real
  error must be structured (§3.3) and correlated with `φ` through an unbounded amount of
  information. AJLW26's leakage theorem (4.2) allows only `O(log λ)` bits, and only for Gaussian
  `T`. So the proof must start with a hop "structured `E` ≈ Gaussian `E`". On a true statement
  the decryptor distinguishes it. So this hop is the WE security itself, and it is
  statement-dependent unless it is split into about `2^128` local hops.
* **No room for witness-indexed hops in linear zero tests.** A positional hybrid would need
  hidden kernels `Λ_t` that contain the valid `α(w)` with `w ≥ t` and none with `w < t`. The
  spans `V_t = span{α(w) : w ≥ t}` form an antitone chain in a `k`-dimensional space. By
  `antitone_chain_few_changes` they change at most `k = poly` times, so at most `poly` of the
  `2^128` positions can be separated by any family of linear kernels. Positional structure needs
  `α(w)` to carry a hidden comparator state, i.e. hidden matrices (GGH15), which leaves the linear
  framework.
* **Attacks summary.** `mask_leak` is avoided at the secret level but returns at the error level
  (`invalid_offset_cancel`). Linear closure gives shortcut and linearization attacks. Evaluation
  collisions are needed in Case I. Statistical attacks on TLWE itself do not apply as long as
  only wide-error vectors are exposed.

## 5. Parameters, for the record

For `Def_WE_CircuitSAT` (`2^12` gates, 128-bit witnesses), BGG+ evaluation of `U_w` has error
growth `β_H = m^{O(d)}` with `d` the depth of `U`. A Case-II design needs short noise `N` with
`‖N‖·β_H ≤ q/(4m²τ)` and wide parts `≥ q/τ`. So `q/τ` and `τ` are both superpolynomial
(`q ≈ 2^{O(d log m)}·τ`). This is within AJLW26's Theorem 4.3 regime (superpolynomial `τ`) but
irrelevant given §3–4.

## 6. Exact remaining gap

1. **(Closed, negative.)** Every TLWE/TDRE design in which the decryptor's processing is public
   and linear (BGG+, key homomorphism, short combinations, rounding) is either
   * Case I: a `w`-dependent trapdoor, i.e. the evaluation-oracle crux or an evaluation
     collision (`pq-we-matrix-collision-barrier`); or
   * Case II: a linear zero test on a hidden error, which has the shortcut and linearization
     attacks, the error-level fixed offset, and no positional hybrids.
2. **(Open, the only remaining route.)** *TLWE zero test for hidden-matrix encodings.* In the
   masked γ⊗-GGH15 candidate (`pq-we-witness-prf-masked-evaluator` §5), replace the final
   small-norm extraction by a public TLWE trapdoor of the last matrix `A_h`, with the last-level
   errors wide. A path value then decodes only if the wide last-level errors of the master and
   constrained left vectors cancel. That is the case exactly when the path's constraint product
   vanishes, because both left vectors share the CPRF block. The missing lemma is the
   **masked two-vector lemma** of that note (witness-indexed, `2^128` hops allowed), now with the
   extra public trapdoor `T_{A_h}` in the view. The first question to settle, before any proof
   attempt, is whether `T_{A_h}` lets an adversary decode single-path values `J Ŝ_w A_h + E_w`,
   which would expose the path products. It does not if every single path carries a wide
   last-level error. Whether the master and constrained left vectors can share that wide error,
   while products of other paths do not cancel it, is open (first instance `h = 2`, two clauses).
3. TLWE contributes nothing beyond (2) toward a proof. Its theorems are polynomial-hop and
   statement-independent, so they can serve only as the per-hop assumption inside a
   witness-indexed hybrid. The local step of that hybrid, which changes the contribution of one
   non-witness path, is the open lemma of (2).

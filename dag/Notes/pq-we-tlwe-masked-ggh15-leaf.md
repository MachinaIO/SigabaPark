---
title: Masked γ⊗-GGH15 WE with a public TLWE leaf trapdoor and wide leaf errors - encodings, exact canonical decoding, where wide errors can live, why they are not per-path LWE noise
refs: [definition:WE_CircuitSAT, definition:GGH15, definition:WE_MaskedGGH15, note:pq-we-witness-prf-masked-evaluator, note:pq-we-masked-evaluator-mechanisms, note:pq-we-masked-overcomplete-leaf, note:pq-we-two-pass-reroute, note:pq-we-multipass-ggh15, note:pq-we-mp2-cryptanalysis, note:pq-we-hybrid-count-barrier, theorem:AdvancedEncryption.WE.GGH15.path_identity, theorem:AdvancedEncryption.WE.MaskedLeaf.hiding_of_separator, theorem:AdvancedEncryption.WE.MaskedLeaf.mask_of_affine_relation, theorem:AdvancedEncryption.WE.MaskedLeaf.affine_relation_of_span]
tags: [witness-encryption, ggh15, candidate, barrier, open-problem]
---
Design-AI sub-task (dd) on `Def_WE_CircuitSAT`. Open PR #78 (note
"pq-we-tlwe-trapdoor-hint-zero-test", not merged when this note is written, so cited by number)
reduces the human's TLWE idea (CPRF outputs in LWE errors; a public trapdoor removes `sᵀA` only
when master and constrained evaluations are close) to one remaining route: the masked γ⊗-GGH15
candidate of `pq-we-witness-prf-masked-evaluator` §5, with the final extraction replaced by a
public trapdoor of the leaf matrix `A_h` from LWE with trapdoor hints (Aggarwal–Jain–Lin–Wu,
ePrint 2026/2927, "AJLW26", read from the full text: Definition 1.1, Theorems 1.1, 3.2, 4.1, 4.2,
4.3, Construction 6.1). This note works that route out.

The four theorem nodes `AdvancedEncryption.WE.TLWEGGH15.*` named below have complete proofs in the
same PR. They are not listed in `refs` because they are not merged yet. Everything else is an
informal argument.

## Answer

1. **The combination is well defined and correct (§1–§2).** Put a wide (TLWE-width) error on the
   leaf level only: full width on the CPRF rows, gated by the leaf plaintext on the constraint rows
   (`(M_{h,b} ⊗ I)F`), none on the mask rows. Publish the AJLW26 public-coin trapdoor of the leaf.
   Then `(u_O − u_C)·D_z` decodes **exactly** to the canonical secret `μ_h = r_0 R_1⋯R_h` on every
   witness path. Decryption is exact, with no rounding.
2. **Question (1), sharing the wide error: yes.** Master and constrained left vectors share the
   CPRF block. Its wide error `S_{<h,z} F^S` is the "CPRF output in the error"; it is identical
   for both and cancels exactly in their difference on *every* path. The gated constraint error
   survives exactly on invalid paths (`wide_gate`). For `h = 2` (and whenever
   `2^{h−1} ≤ n'`), no combination of other paths cancels it: every decodable combination is
   supported on witness paths (`decodable_support`). In general a cancellation is exactly an
   affine relation among the gated rows, the object of `pq-we-masked-overcomplete-leaf`.
3. **What TLWE changes (§4).** It lets the leaf matrix and its trapdoor be public while keeping
   the leaf step of the root-first proof of `pq-we-masked-overcomplete-leaf`. That step becomes
   "TLWE hop, then `hiding_of_separator`". So the provable class is unchanged: the `h = 2` instances,
   two clauses included, and the cut-lemma class. A variant that publishes a trapdoor of the mask
   rows `A_h^{mask}` only and keeps the other leaf rows hidden has the same decoding and the same
   proof from plain LWE, with no TLWE and no wide error. **TLWE is needed only if the whole leaf is
   made public.**
4. **No "noise as LWE noise" handle (§5).** The wide error is linear in each path's gated
   constraint row, so every affine relation that removes the pad removes the wide error too
   (`affine_relation_kills_linear_pad`). Wide errors cannot sit at inner levels: their
   cancellation set is closed under shared prefixes (`cancel_prefix_closed`), so they can gate
   only prefixes that are already dead, which is the cut-lemma region. The gap of
   `pq-we-masked-overcomplete-leaf` (the end step must use the *inner-level* noise) and the
   consistency barrier of `pq-we-two-pass-reroute` are untouched. The wide error vanishes on every
   witness path, and the trapdoor makes witness noise exact.
5. **Attacks (§6).** No new attack. Single paths, single left vectors and inclusion–exclusion
   combinations do not decode. Zeroizing needs witness paths, which a false statement does not
   have. On true statements the trapdoor gives exact zeros, one more dimension than the
   differences already gave. One consistent proof move is lost: an LWE step on the mask leaf rows.
6. **Remaining gap (§8).** Unchanged: the overcomplete cut lemma of
   `pq-we-masked-overcomplete-leaf` §10 (equivalently the masked two-vector lemma with `2^128`
   witness-indexed hops), now with `(A_h, R_h)` in the view. It is no harder for every proof that
   chooses the mask leaf rows itself, which includes all proofs attempted so far.

## 1. Exact encodings

Notation follows `pq-we-witness-prf-masked-evaluator` §5 and `pq-we-masked-overcomplete-leaf` §1
(vocabulary `Def_GGH15`, `Def_WE_MaskedGGH15`). The levels `1..h` read the variables of the CNF
`Ψ_φ`. `M_{i,b}` is CVW18's diagonal clause BP (Construction 6.4): `(M_{i,b})_{kk} = 0` iff bit
`b` of variable `i` satisfies clause `k`. So `M_z = ∏ M_{i,z_i}` has `(M_z)_{kk} = 1` iff `z`
falsifies `k`.

* **Secrets.** `Ŝ_{i,b} = diag(R_i, M_{i,b} ⊗ S'_{i,b}, S_{i,b})`: the mask block (bit-independent
  `R_i`), the twisted constraint block (`S'_{i,0} ≠ S'_{i,1}`), and the CPRF block. Inner secrets
  are small. **Leaf secrets `R_h, S'_{h,b}, S_{h,b}` are uniform mod `q`.** This is allowed
  because, by `AdvancedEncryption.WE.GGH15.path_identity`, the noise of a path is
  `∑_{j<h} Ŝ_{<j} E_j D_{>j}`, and the leaf secret never multiplies an error.
* **Matrices.** `A_0, …, A_{h−1}` are hidden, with trapdoors held by the encryptor. The leaf is
  stacked from independent public-coin samples (AJLW26 Fig. 1 / Thm 3.2):
  `A_h = [A^{mask}; A^{1}; …; A^{K}; A^{bot}]`, each block `[B | BR + G_τ]` with its own public
  binary `R`.
* **Inner encodings.** `D_{i,b} ← A_{i−1}^{-1}(Ŝ_{i,b} A_i + E_{i,b})` with narrow `E`, for
  `i < h`.
* **Leaf encodings.** `D_{h,b} ← A_{h−1}^{-1}(Y_{h,b})`, where `Y_{h,b}` has three row blocks:
  * mask rows: `R_h A^{mask} + N_b`, narrow;
  * constraint rows of clause `k`: `(M_{h,b})_{kk}·(S'_{h,b} A^{k} + F_{k,b})`. So rows with
    `(M_{h,b})_{kk} = 0` are zero up to narrow noise, and the live rows are TLWE samples with wide
    `F_{k,b} ← D_{Z,σ}`, `σ ≥ τ^{c−1}·ω(√log λ)` (AJLW26 Thm 4.1);
  * CPRF rows: `S_{h,b} A^{bot} + F^S_b`, wide.
* **Left vectors.** `u_O = J_O A_0` and `u_C = J_C A_0` with `J'_O − J'_C = 1_n ⊗ (e_mask − j_C)`
  (the rank-one repair) and the identity on the CPRF block in both.
* **Ciphertext.** `(u_O, u_C, {D_{i,b}}, {R of every leaf block}, Ext(μ_h) ⊕ msg)` for a
  randomness extractor or hard-core function `Ext`.

**Instance `h = 2`, two clauses.** Over two variables, a two-clause CNF is unsatisfiable only if it
is `(z_1) ∧ (¬z_1)` or `(z_2) ∧ (¬z_2)`.

* For `(z_1) ∧ (¬z_1)`: `M_{1,0} = diag(1,0)`, `M_{1,1} = diag(0,1)`, `M_{2,b} = I`.
* For `(z_2) ∧ (¬z_2)`: `M_{1,b} = I`, `M_{2,0} = diag(1,0)`, `M_{2,1} = diag(0,1)`. Only the
  clause-1 leaf rows are live for `b = 0`, and only the clause-2 rows for `b = 1`.

The four path values are computed in §2. A satisfiable control is `(z_1 ∨ z_2) ∧ (¬z_1 ∨ ¬z_2)`,
with witnesses `01` and `10`.

## 2. Canonical decoding with the leaf trapdoor

Write `v_{k,p} = s'_{0,k} S'_{<h,p}` for the hidden gated prefix row of clause `k` and prefix `p`.
Write `Y_{k,b} = S'_{h,b} A^{k} + F_{k,b}` for the live leaf block, and `ρ = r_0 R_{<h}`. From
`path_identity`, the value read with `J_Δ = J_O − J_C` (all `n` rows are equal) is

`y_z = μ_h A^{mask} − ∑_{k ∈ U(z)} v_{k,p(z)} Y_{k,z_h} + e_z`,

* `μ_h = ρ R_h`;
* `U(z)` is the set of clauses that `z` falsifies;
* `e_z = ρ N_{z_h} + ∑_{j<h} J_Δ Ŝ_{<j} E_j D_{>j}` is narrow.

Two facts give this form.

* The CPRF block cancels in `J_Δ`, together with its wide error.
* The constraint block's wide error is gated by the whole path product. By `wide_gate` (Lean),
  `(X ⊗ Y)((M ⊗ I)F) = ((XM) ⊗ Y)F`. With `X = j_C M_{<h}`, the surviving wide part of clause
  `k` is `[(M_z)_{kk} = 1]·v_{k,p}F_{k,b}`.

**Decryption.** On a witness `U(z) = ∅`, so `y_z = μ_h A^{mask} + e_z`. `TdInvert(A^{mask}, R^{mask})`
returns `(μ_h, e_z)` when `‖e_z‖ ≤ t ≤ q/(4mτ)` (AJLW26 Thm 3.2, with the two-sided guarantee of
its Remark 3.3). The key `Ext(μ_h)` is the same for every witness. This is the masked evaluator's
"witness dependence removed", now exact.

**Invalid paths.** `y_z` carries `v_{k,p}Y_{k,b}` for some `k`, which contains the wide
`v_{k,p}F_{k,b}`. It is outside the decoding radius, and TdInvert returns `⊥`.

**Single left vectors.** `u_O` alone carries `S_{<h,z}F^S` (wide), and so does `u_C`. Neither
decodes on any path. Without the wide CPRF error, `y^O_z·T^{bot}` would strip the CPRF pad of
`u_O`'s value and leave `μ_h A^{mask} T^{bot}` plus narrow noise (the trapdoor projection of §6),
and with a trapdoor of the whole stacked leaf `u_O` would decode to `(μ_h, 0, S_z)` outright. So **the CPRF-block wide error is the shared one**: it is exactly
the human's "CPRF output in the error", common to master and constrained evaluation on every path.
The closeness that gates decoding comes from the constraint block, not from the CPRF.

**`h = 2` values.**

* `(z_1)∧(¬z_1)`: `y_{0b} = μA^{mask} − v_{1,0}Y_{1,b} + e` and `y_{1b} = μA^{mask} − v_{2,1}Y_{2,b} + e`.
  Each path owns its leaf block `(k, b)`.
* `(z_2)∧(¬z_2)`: `y_{p0} = μA^{mask} − v_{1,p}Y_{1,0} + e` and `y_{p1} = μA^{mask} − v_{2,p}Y_{2,1} + e`.
  Two paths share each leaf block, with rows `v_{k,0}`, `v_{k,1}`, which are independent for
  `n' ≥ 2`.

## 3. Where the wide error can live

* **Not on mask rows.** A wide mask error contributes `ρF^{mask}_{z_h}` to every witness value.
  Witnesses ending in different bits would decode differently, or not at all. A shared `F^{mask}`
  would make the canonical value `ρ(R_hA^{mask} + F^{mask})` undecodable. So the mask leaf rows are
  narrow.
* **Constraint rows: only gated by the leaf plaintext.** An ungated wide error survives on any
  witness whose prefix has `M_{<h} ≠ 0`, that is, a clause satisfied only at the last variable.
  `(M_{h,b} ⊗ I)F` is gated exactly by `M_z` (`wide_gate`).
* **Only at the leaf.** A wide part `W` of an inner error `E_j` reaches the value as
  `J Ŝ_{<j} W_{j,z_j} D_{>j}`. `D_{>j}` is a long Gaussian product, so the term is useless unless it
  cancels exactly. Exact cancellation depends on `z_0..z_j` only, so the set where it cancels is
  closed under sharing a prefix with a valid path (`cancel_prefix_closed`, Lean). The encoder must
  make it cancel on every prefix that *some* witness extends. It does not know these prefixes
  (deciding them is NP-hard), except for prefixes that already falsify a clause inside the first
  `j + 1` variables. Those are exactly the prefixes where the cut lemma of
  `pq-we-masked-overcomplete-leaf` §6 already proves security from LWE. So inner wide errors add
  nothing.

## 4. What TLWE changes in the proofs

* **The leaf step with a public trapdoor.** The root-first proof of
  `pq-we-masked-overcomplete-leaf` (phase 1, projection lemma PL at every level, then the
  statistical leaf step) ends with `hiding_of_separator`, which needs the leaf constraint matrix
  uniform and unused elsewhere. Here `A^{k}` is public, with a trapdoor. Insert one hop per live
  block: `(A^{k}, R^{k}, S'_{h,b}A^{k} + F_{k,b}) ≈_c (A^{k}, R^{k}, U_{k,b})`. This is AJLW26
  Thm 4.1 with a uniform matrix secret: a row-by-row hybrid, where the reduction makes the other
  rows itself from public `A^{k}`. The CPRF rows are handled in the same way (phase 1). After the
  hops, `Y_{k,b}` is uniform and used only in the path values. `hiding_of_separator` then applies
  with `Y` in place of `A^{con}`. The reduction samples everything else, including `A_{h−1}`'s
  trapdoor and the mask block `(A^{mask}, R^{mask})`.
* **`h = 2`.** For `(z_1)∧(¬z_1)` every path owns its block, so a point separator exists per path.
  For `(z_2)∧(¬z_2)` the rows `v_{k,0}`, `v_{k,1}` are independent, so a separator `ℓ` with
  `v_{k,p}ℓ = 1` exists. Both instances are therefore proved: PL, TLWE hops, statistical leaf.
  In general the provable class is exactly the one of the original candidate: separator
  instances and the cut-lemma class, all decidable in time `2^L·poly`, as
  `pq-we-hybrid-count-barrier` requires of polynomial-hop proofs.
* **Without TLWE.** Publish only `R^{mask}` and keep `A^{1..K}`, `A^{bot}` hidden and uniform.
  * Decoding is unchanged: valid values are `μ_h A^{mask} + e_z`.
  * Invalid values carry `v·S'_{h,b}A^{k}` with a hidden uniform `A^{k}`, so they do not decode.
    No wide error is needed.
  * The proof is the original one verbatim, with `(A^{mask}, R^{mask})` sampled by the reduction.
  * So the trapdoor's only gain is exact canonical decoding. TLWE is the price of publishing the
    rest of the leaf, and that buys nothing for security.
* **One consistent move is lost.** In the original design, with `A^{mask}` public and no
  trapdoor, `R_hA^{mask} + N_b → U + N_b` (the same `U` for both bits) is an LWE hop that keeps
  every witness value equal. So it passes the consistency test of `pq-we-two-pass-reroute` §4.
  With `R^{mask}` public this hop is false. No attempted proof uses it.

## 5. Is the wide error the missing "noise as LWE noise"?

No. There are three exact reasons.

1. **Linear in the gated row.** On each last bit the leaf contribution is `c_z·Y_b` with
   `Y_b = (I⊗S'_{h,b})A + F_b`. The wide error is part of the pad, not independent per-path noise.
   `affine_relation_kills_linear_pad` (Lean): if `∑α_z = 1` and `∑α_z c_z = 0`, then
   `∑α_z y_z = m + ∑α_z e_z` for any linear `L`, wide error included. The overcomplete regime of
   `pq-we-masked-overcomplete-leaf` §3 (`affine_relation_of_span`) has such relations whenever
   `2^{h−1}` exceeds the width. So the end step must still hide `m` behind `∑α_z e_z`, the *inner*
   narrow GGH15 noise. That noise cannot be made wide (§3).
2. **Consistency barrier unchanged.** The barrier of `pq-we-two-pass-reroute` §4 is about hidden
   rows `δ_i` at pass-1 levels, used by witness paths. The wide error is leaf-only and vanishes on
   every witness path (`wide_gate`), so no wide-error move touches a witness value. That is why the
   leaf hops are consistent, and also why they cannot reach `δ_i`. The trapdoor makes the barrier
   slightly sharper: witness values decode to the exact `μ_h` and the exact noise `e_w`.
3. **Masked-leak lemma `ML_i` unchanged.** `ML_i` plants `δ` at an inner level. The leaf TLWE hops
   are available in its proof but act on the leaf block only, and `δ` reaches the leaf as an inner
   noise term `δ D_{>i+1}`, which is narrow.

So TLWE supplies hardness exactly where the old proof already had a statistical step (hidden leaf),
and nowhere else.

## 6. Attacks

* **Single-path decoding** (PR #78's first question). Every single path, under either left vector
  or `J_Δ`, carries a wide term on a false statement. Nothing decodes, so path products are not
  exposed.
* **Linear closure (PR #78).** The decodable set is closed under short combinations. A
  combination decodes iff its wide part vanishes for every `(k, b)`, i.e. iff
  `∑_{z_h=b} α_z [k∈U(z)] v_{k,p(z)} = 0`. Then the pad vanishes too, and the decoded secret is
  `(∑α_z)μ_h`. With independent rows (`h = 2`, or `2^{h−1} ≤ n'`), `decodable_support` (Lean)
  forces `α` onto witness paths, so on a false statement only `α = 0` decodes. Beyond the width
  horizon, the decodable combinations are the affine relations of `mask_of_affine_relation`,
  required now to be exact mod `q`, with `‖∑α_z e_z‖ ≤ t`. This is the same short-relation problem
  as the "low-rank plus noise" attack of `pq-we-witness-prf-masked-evaluator` §5, item 5, with the
  rounding margin replaced by `t ≈ q/(4mτ)`.
* **Inclusion–exclusion** (CVW18 Remark 10.3). Blocked as before: twisting makes `v_{k,p}`
  prefix-specific, so `+1, +1, −1` combinations leave wide terms.
* **Trapdoor projections.** `y_z·T^{k}` removes `A^{k}` but leaves `v F T^{k} mod q`, which is
  pseudorandom by TLWE. This is where the wide error is *needed* once `R^{k}` is public: with narrow
  `F`, `y_z T^{k}` would strip the pad of an invalid path, leaving a noisy multiple of `μ_h`.
  `y_z T^{mask}` removes only the mask.
* **Zeroizing** (CVW18 §9, CCHKL, CLLT16). These need decodable (zero) paths. On a false
  statement there are none (above). On true statements the trapdoor reveals each witness's exact
  noise `e_w`. Previously only the differences `e_w − e_{w'}` were available, so rank attacks gain
  one dimension. That matters only for hops that must hold on true statements (reroutes), and
  `pq-we-mp2-cryptanalysis` §3, caveat 2, already applies to those.
* **Mixed inputs.** Read-once with a fixed statement. Unchanged.
* **TLWE itself.** The leaf blocks satisfy Thm 4.1's hypotheses as stated. The secret is uniform,
  and `σ ≥ τ^{c−1}ω(√log λ)` is far above the radius `t`. Hardness rests on LWE in dimension
  `n_h/log q` with ratio about `τ m^{1.5}`. Thm 4.2's leakage form (Gaussian `T`, polynomial `q`)
  is not used: GGH15 depth needs superpolynomial `q`.

## 7. Costs

* **Without TLWE (partial trapdoor).** The decoding radius `t ≈ q/(4mτ)` replaces the rounding
  margin, so with `τ = 2`, `log q` grows by about `log(8m)` bits. The trapdoor of `A^{mask}` needs
  `m ≥ 2 d_R log q` columns (AJLW26 Thm 3.2), which the multi-pass parameters (`pq-we-multipass-ggh15`) already
  meet. The size is essentially that of MP2/MP3.
* **With TLWE (public leaf).** Thm 4.1 loses a factor `log q` in dimension (`n' log q ≤ n`). So
  each leaf block needs `n_h ≈ n'·log q` rows, and the leaf width `m_h ≥ 4 n_h log q` grows by
  `log² q` relative to MP2.
  * With `log q ≈ 2^{16.5}`, the leaf encodings `D_{h,b} ∈ Z^{m×m_h}` grow by roughly `2^{33}`.
  * This is still below the `2^{188}`-bit brute-force baseline, but buys no security (§4).
  * Only the leaf grows, because `D_{h,b}` may be rectangular.

## 8. Remaining gap, stated precisely

* **Construction.** Recommended: partial trapdoor, exact canonical decoding, `ciphertext ≈ MP2`.
  The TLWE variant (§1) is equivalent for every proof technique known to us.
* **Open lemma.** The overcomplete cut lemma of `pq-we-masked-overcomplete-leaf` §10, or
  equivalently the masked two-vector lemma of `pq-we-witness-prf-masked-evaluator` §6 with up to
  `2^{|w|}` witness-indexed hops. Add to the view:
  * the public `(A^{mask}, R^{mask})` (partial variant);
  * or all leaf blocks and their `R` (TLWE variant).

  For every proof in which the reduction chooses the mask leaf rows, the partial variant follows
  from the original lemma. This covers every proof attempted in the DAG: root-first, PLR,
  reroute, and the equality-cube flip of open PR #71.
* **What a proof must contain.** A computational step on the *inner* GGH15 noise of one path (the
  end step of `pq-we-masked-overcomplete-leaf` §3), consistent in the sense of
  `pq-we-two-pass-reroute` §4. TLWE does not supply it:
  * wide noise is either leaf-only and linear in the gated row (§5.1);
  * or it lives at an inner level and can only gate dead prefixes (§3).
* **Closed by this note.** Question (1) is answered positively (shared CPRF wide error, gated
  constraint wide error, no cancellation for `h = 2`). The `h = 2` two-clause instances are proved
  in the TLWE variant (§4). The trapdoor creates no new attack on false statements (§6).

## Formal results of this PR

* `AdvancedEncryption.WE.TLWEGGH15.wide_gate`: `(X ⊗ Y)((M ⊗ I)F) = ((XM) ⊗ Y)F`. The gated wide
  error survives exactly as `M_z` does.
* `AdvancedEncryption.WE.TLWEGGH15.affine_relation_kills_linear_pad`: an affine relation among
  gated rows removes every linear term, wide error included.
* `AdvancedEncryption.WE.TLWEGGH15.decodable_support`: with independent gated prefix rows and
  injective wide blocks, decodable combinations are supported on valid paths.
* `AdvancedEncryption.WE.TLWEGGH15.cancel_prefix_closed`: an inner-level wide error that cancels
  on every valid path cancels on every path sharing its first `j + 1` bits with a valid path.

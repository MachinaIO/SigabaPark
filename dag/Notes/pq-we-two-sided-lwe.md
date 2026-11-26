---
title: Two-sided hidden-row LWE for multi-pass GGH15 WE - the standalone statement, a decodable-continuation attack, and why flooding, TLWE lossiness and hinted LWE miss it
refs: [definition:WE_CircuitSAT, definition:GGH15, definition:WE_MaskedGGH15, definition:SuccinctLWE, definition:DecomposedLWE, note:pq-we-two-pass-reroute, note:pq-we-multipass-ggh15, note:pq-we-mp2-cryptanalysis, note:pq-we-split-lemma-attempts, note:pq-we-ggh15-vocabulary-open-lemmas, note:pq-we-plr-hop-rank-and-erase, note:pq-we-masked-overcomplete-leaf, theorem:AdvancedEncryption.WE.Reroute.multipass_subtree_hop, theorem:AdvancedEncryption.WE.Reroute.two_pass_cross_rank_le, theorem:AdvancedEncryption.WE.Reroute.kilian_relations_iff, theorem:AdvancedEncryption.WE.TwoSided.decoded_defect_attack, theorem:AdvancedEncryption.WE.TwoSided.two_child_preimage_consistency, theorem:AdvancedEncryption.WE.TwoSided.decryption_recovers_noise]
tags: [witness-encryption, ggh15, barrier, open-problem, assumption]
---
Design-AI sub-task (bb) on `Def_WE_CircuitSAT` (128-bit witnesses, NAND circuits with `2^12`
gates, `λ = κ = 128`). The multi-pass candidate MP2/MP3 (`pq-we-multipass-ggh15`) has two open
lemmas that need a new technique:

* the masked-leak lemma `ML_i` of `pq-we-two-pass-reroute` §7, blocked by its consistency
  barrier (§4 there);
* the fat sibling-pad lemma (FSP) of open PR #71 (note "pq-we-equality-cube-flip", cited by
  number because it is not merged when this note is written).

This note tries to build that technique. It (1) states standalone two-sided LWE statements,
(2) tries to reduce them to LWE, to LWE with trapdoor hints (TLWE, ePrint 2026/2927, read from
the full text) and to the hinted assumptions of the DAG, and (3) attacks them. The three theorems
marked "Lean" have complete proofs; everything else is an informal argument. Notation follows
`pq-we-two-pass-reroute` §1–§2 (scalar-row model after root-first projection).

**Answer.**

1. **No local standalone statement works (§2).** Make the hidden row `δ`, its two zero children
   and its masked leak into one standalone game. That game falls into one of two cases,
   according to what follows level `i+1`:
   * **No continuation, or one that cannot be decoded:** provable from LWE (§2.1), but it does
     not imply `ML_i`.
   * **A continuation that can be decoded** (anyone holding a trapdoor of `A_{i+1}`): **false**
     whenever more than `k+1` prefixes reach the cut, where `k` is the dimension of the pads.
     The attack is exact linear algebra over `Q` on the decoded noises
     (`TwoSided.decoded_defect_attack`, Lean).

   `ML_i` sits strictly between the two. Its continuation can be decoded only along witness
   completions, and with `c ≥ 2` passes each prefix has its own completions. **The cleanest
   faithful standalone statement is `ML_i` itself**, made uniform over the CNF (§1). No new open
   node is added: it is the open node `Reroute.multipass_subtree_hop`.
2. **A barrier for reductions that hold a trapdoor (§3).** Any reduction that can decode at
   level `i+1` at the decryption noise level could run the attack on its own output. This
   includes every reduction that samples `A_{i+1}` with a trapdoor to simulate the downstream
   encodings. So it cannot be a reduction from a hard problem. Without a trapdoor, "preimage
   first" simulation of the two children is impossible for square preimages
   (`TwoSided.two_child_preimage_consistency`, Lean). **A proof must obtain preimages of
   structured honest-zero targets without the ability to decode.** Evasive LWE postulates exactly
   that. Succinct, decomposed and tensor LWE do not supply it for GGH15 levels.
3. **Specific strategies (§4).**
   * Noise flooding cannot hide the defect: noise that is common to both children through `D_b`
     contributes nothing to it (Lean).
   * TLWE lossiness needs `σ_e σ_t ≳ q·m`, but honest decryption *is* TLWE's attack and must
     succeed (`TwoSided.decryption_recovers_noise`, Lean).
   * The leftover hash lemma does not apply: the obstruction is exact linear dependence over `Q`,
     not low entropy.
   * The tensor-LWE route has no "zero samples".
4. **The FSP is not affected (§5).** Its meeting block has a zero on one child only. The defect
   needs two zero children, and preimage-first simulation is valid for one. FSP stays the most
   promising target. Its standalone form is "LWE whose public matrix is a hidden twisted product
   family" (product-LWE): it is provable when the prefix rows are independent, and open in the
   overcomplete case.

## 0. The object: a hidden row with two zero children and a masked leak

In the hybrid `G_{i+1}` of `pq-we-two-pass-reroute` §1, the chain state `eq_i` goes to `lt` on
both bits. Put `δ := ℓ^{eq}_i − ℓ^{lt}_i ∈ Z_q^{1×m}`, which is uniform. Then:

* **(right, two children)** `δ D_b = f_b` for `b ∈ {0,1}`, where
  `f_b = ρ_i(E^{eq}_{i+1,b} − E^{lt}_{i+1,b})` is small. Here `D_b := D_{i+1,b}`.
* **(left, masked leak)** the chain prefix value is `v_t = ℓ^{lt}_i + δ + c_t A^{con}_i + e_t`.
  Every other prefix `x` at cut `i` has `v_x = ℓ^{lt}_i + c_x A^{con}_i + e_x` (lt prefixes; eq
  and gt are analogous).

The comparison hybrid `G'` (noisy copy, `≈_s G_i`) has `δ` short, so `δ` is absorbed into the
noise. Write `c'_x := (1, c_x)` and `E'_b := [E^{lt}_{i+1,b}; E^{con}_{i+1,b}]`, so that the
`lt`-row noise is the constant coordinate. Then the noise of `v_x D_b`, relative to the GGH15
target, is

`N_b(x) = c'_x E'_b + e_x D_b + [x = t]·f_b`

in `G_{i+1}`, and the same without the last term in `G'`/`G_i`.

* **Noise only.** The two hybrids differ only in noise; all decrypted labels agree
  (`pq-we-two-pass-reroute` §2).
* **Overcomplete.** `2^i ≫ k := dim A^{con}_i + 1`, so `c'_t ∈ span_Q {c'_x : x ≠ t}`.

## 1. The standalone statements

**TSR (two-sided row), parameterised by what follows level `i+1`.** The challenger samples:

* the level matrix `A_i = [ℓ; δ; P]`, uniform and hidden, with `P ∈ Z_q^{(k−1)×m}` the pad rows;
* `D_b ← A_i^{-1}([Y^ℓ_b; f_b; Y^P_b])` for `b ∈ {0,1}`, with `f_b ← χ`;
* the leaks `v_x = ℓ + c_x P + [x = t]·β·δ + e_x` for the `2^i` prefixes `x`;
* a **continuation** `C` that lets the adversary use the targets `Y_b`.

The challenge bit is `β`; with `β = 0` the row `δ` is short instead.

Three instances:

* **TSR_loc:** `C` is empty and the `Y_b` are uniform.
* **TSR_dec:** `Y_b = S_b A_{i+1} + E_b`, and `C` is a trapdoor of `A_{i+1}` (or any LWE decoder
  for `A_{i+1}` at the GGH15 noise level).
* **TSR_Ψ:** `C` is the masked γ⊗-GGH15 encoding, levels `i+1 … h`, of the multi-pass program
  of `positionalView` for an **adversary-chosen** CNF `Ψ` that contains the equality clauses.
  The rows `P` and the `c_x` are its constraint rows.

All three are **falsifiable**: the challenger is efficient given `Ψ`, and a distinguisher can be
checked. They are **independent of the statement being encrypted to**: one assumption covers
every `Ψ`, and the WE statement is never a parameter of the assumption. TSR_Ψ quantifies over
programs only through the adversary's choice of `Ψ`, with a fixed local edit. So it is not an
iO-type "all equivalent programs" assumption. It is `ML_i` made uniform over `Ψ`: any reduction
of `ML_i` that does not use `Ψ` (every CVW18 move is of this kind) proves TSR_Ψ, and
conversely. **TSR_Ψ is the faithful standalone statement.** The open node
`Reroute.multipass_subtree_hop` already carries it, so this note adds no new open node.

The question of the sub-task is whether some *local* statement, without the downstream program,
implies TSR_Ψ. §2 answers it negatively.

## 2. The local statements are either too weak or false

### 2.1 TSR_loc is provable from LWE (and too weak)

* The targets `Y^P_b` are uniform and used nowhere else, so CVW18 Lemma 4.1 drops the `P` rows
  from `D_b` (statistically).
* `P` is then used only on the left, so LWE with secret `P` and public `c_x` (with independent
  `c_x`, or the hybrid over a basis) makes `c_x P + e_x` uniform. This hides `δ` in `v_t`.
* `δ` is then used only on the right, so CVW18 Lemma 4.4 (`pq-we-split-lemma-attempts` §(2),
  "for an arbitrary target") makes `D_b` Gaussian.

The same holds when `A_{i+1}` is **public but has no trapdoor**: LWE with secret `S_b` and public
`A_{i+1}` makes `Y^P_b` uniform first.

TSR_loc does not imply `ML_i`. Its reduction would have to simulate the downstream encodings,
which contain honest zeros through `eq_i`.

**Aside (the NTRU view of a two-child zero row).** Without the leak, `(D_0, D_1)` already differs
*statistically* between `β = 1` and `β = 0`:

* `(f_0, f_1)` is a short vector of the q-ary lattice `{(x, x·D_0^{-1}D_1 mod q)}`;
* for `β = 1` it lies outside the real span of the rows of `[D_0 | D_1]`;
* for `β = 0` (`δ` short) it is `δ[D_0 | D_1]`, which lies inside that span.

Lemma 4.4 hides this computationally, as long as `δ` is not leaked. The gap is a planted-vector
(NTRU-type) uSVP. Its dimension is `≈ m ≈ 2^{40}` and its gap is `≈ q/(σχ√m)`, so with
`log q ≪ m·log δ_β` lattice reduction does not reach it. This is the computational content
that every proof must preserve: an unbounded adversary sees `δ` (`pq-we-two-pass-reroute` §3).

### 2.2 TSR_dec is false: the decoded-defect attack

With a trapdoor of `A_{i+1}`, decode each `v_x D_b` (`b = 0, 1`) to its exact integer noise
`N_b(x)`. Decoding succeeds because correctness of the WE forces `‖N_b(x)‖·‖D_{>i+1}‖ < q/4`,
which is far inside the trapdoor's decoding radius. Over `Q`, with `D_b` invertible, put

`Φ(x) := N_0(x) D_0^{-1} − N_1(x) D_1^{-1}`.

* The term `e_x D_b` cancels, and `Φ(x) = c'_x (E'_0 D_0^{-1} − E'_1 D_1^{-1}) + [x = t]·φ`,
  with `φ := f_0 D_0^{-1} − f_1 D_1^{-1}`.
* Solve `c'_t = Σ_{x≠t} γ_x c'_x` over `Q`. This is possible once the other prefixes span `Q^k`,
  i.e. as soon as `2^i − 1 ≥ k` for generic rows.
* Put `α_t = 1` and `α_x = −γ_x`. Then `Σ_x α_x Φ(x)` is:
  * **exactly `0`** in `G'`/`G_i`;
  * **exactly `φ`** in `G_{i+1}`, and `φ = 0` iff `f_1 = f_0 D_0^{-1} D_1`, which is a
    probability-`≈ 0` event for independent Gaussians.

**This is `AdvancedEncryption.WE.TwoSided.decoded_defect_attack` (Lean)**, stated over any field
for the exact identities. The attack is the one-pass rank jump (#56 §1) in its sharpest form: it
needs only one cut, two children and decodability.

`ML_i` escapes it only because, in the real view, the noises `N_b(x)` are never decoded at level
`i+1`. They are only seen summed with all later noise terms, along witness completions that are
different for every prefix `x` (equality clauses). Those are exactly the variable-partition
structures of `pq-we-two-pass-reroute` §6, with rank bounded by `t^{2c−1}`
(`Reroute.two_pass_cross_rank_le`).

### 2.3 Consequence

* The dividing line between "provable" and "false" is **decodability of the level after the
  hidden row**.
* `ML_i` holds only because decoding is restricted to re-reading paths.
* A local two-sided statement can therefore imply `ML_i` only if it already contains a
  continuation with prefix-specific decoding, i.e. the multi-pass encoding itself.

**There is no "bilinear LWE" statement about `(A, D, sᵀA + e)` alone that implies `ML_i` and is
not false.**

## 3. A barrier for reductions that hold a trapdoor

Let `R` be a reduction that, on its challenge, outputs `G_{i+1}` on one challenge law and
`G'`/`G_i` on the other, and that knows a trapdoor of the `A_{i+1}` it outputs (or can decode at
level `i+1` at the decryption noise level).

* Then `challenge ↦ Stat(R(challenge))`, where `Stat` is the §2.2 statistic, distinguishes the
  two challenge laws with advantage `≈ 1`.
* So `R`'s challenge is not hard.
* This covers every reduction that samples `A_{i+1}` with a trapdoor in order to simulate the
  downstream preimages `D_{>i+1}`, the usual way GGH15 hybrids are simulated.

The only trapdoor-free way to simulate preimages of *structured* targets is "preimage first":
sample `D` Gaussian, then define `A := Y·D^{-1}`. With `A` hidden this is statistically exact for
one target. For the two children of the same matrix it is possible only when
`Y_0 D_0^{-1} = Y_1 D_1^{-1}` (`TwoSided.two_child_preimage_consistency`, Lean).

* On the `δ` row this would require `f_1 = f_0 D_0^{-1} D_1`, which is not small.
* For rectangular preimages (`2m' ≤ m`) it works, but GGH15 levels are square, since every
  level matrix has `m` columns.

**Consequence.** A proof of `ML_i` must supply downstream preimages of honest-zero targets while
denying the reduction decoding at level `i+1`. Among the hinted assumptions:

* **Evasive LWE** postulates exactly this, and is excluded.
* **Succinct LWE** (`Def_SuccinctLWE`) gives `T ← [I_ℓ ⊗ B | W]^{-1}(I_ℓ ⊗ G)`: preimages for
  the stacked matrix only. These do not give preimages under `B` of arbitrary structured targets
  without the `W`-shift. A GGH15 whose levels have this stacked shape is a possible redesign; we
  did not find one compatible with canonical decryption, and the redesign is open.
* **Decomposed LWE** (`Def_DecomposedLWE`; worst-case hardness in ePrint 2026/2443 was not
  checked here) gives samples `sᵀA_iB_j + sᵀG·δ_{ij} + e`. It has no preimage hints and no zero
  samples.
* **Tensor LWE** gives samples `sᵀ(r ⊗ A) + e` with public short `r`. Its two-sidedness is public
  on one side and reduces to LWE because every sample keeps a fresh pseudorandom part.
* **None of these has "zero samples"**, i.e. visible exact relations `δ D_b ≈ 0` of the secret,
  and `ML_i` has two per hidden row.

## 4. The suggested strategies, one by one

1. **Noise flooding with large noise.** Two places are candidates for flooding noise:
   * *The level-`i` noise `e_t`.* Its contribution to the two children is `(e_t D_0, e_t D_1)`,
     which lies on an `m`-dimensional subspace of `Z^{2m}`. The defect functional
     `(u_0, u_1) ↦ u_0 D_0^{-1} − u_1 D_1^{-1}` vanishes on it identically (the middle step of the
     Lean proof). So no width of `e_t` floods `φ`.
   * *Per-child fresh noise.* The only such noise is the pad noise `c'_t E'_b`. When
     `c'_t ∈ span_Q{c'_x}`, it is a fixed `Q`-linear function of the other prefixes' pad noises,
     not fresh. Flooding works exactly when `c'_t` is outside that span, i.e. in the
     non-overcomplete regime `2^i ≤ k`, where the projection lemma already works.

   **Stops at overcompleteness.**
2. **Lossiness / entropic LWE (TLWE, ePrint 2026/2927).**
   * *What TLWE proves.* `(A, T, sᵀA + e)` is pseudorandom given a full trapdoor `T`, for
     `σ_t ≥ m·τ·ω(√log n)` and `σ_e ≥ (q/τ)·ω(√log n)` (its Theorem 1.1). The idea is that a
     wide-noise gadget sample is lossy in `s`, and then entropic LWE applies.
   * *Hence it needs* `σ_e·σ_t ≥ q·m·ω(log n)`. Its "textbook attack" multiplies the sample by
     `T` and reads off `eT` when `σ_eσ_t = o(q/√m)`.
   * *Map to the WE.* The analogue of `T` is the decryption chain `D_b D_u` of a witness through
     `eq_i`. Correctness requires `‖e_t D_b D_u‖ < q/4`, and then the noise is recovered exactly
     (`TwoSided.decryption_recovers_noise`, Lean, the centred-lift identity). So the WE always
     sits in the regime where TLWE's attack succeeds.
   * *Error leakage does not help.* TLWE's error-leakage extension tolerates only `O(log λ)`
     bits of leakage on `e`. Decryptions leak linear images of the noise of full dimension.
   * *Entropic LWE does not help.* Given `(D_0, f_0)`, `δ = f_0 D_0^{-1}` is determined, so the
     entropy of `δ` is that of `f_0`, which the decryptions expose.

   **Stops at correctness.**
3. **Leftover hash on the twisting secrets.** The obstruction is not entropy but exact
   `Q`-linear dependence of the pad rows `c'_x` (§2.2). Hashing makes `c'_t E'` close to uniform
   only modulo `q`, while zero-tested values are integers. **Stops.**
4. **Through tensor LWE, or a "bilinear LWE" proven from LWE.** Write `H := D_0^{-1}D_1`. In the
   language of LWE samples, `ML_i` at one node says: LWE-type samples whose error contains an
   NTRU-correlated pair `(f_0, f_0 H)`, with `H` public, are indistinguishable from samples
   without that pair. Two observations:
   * Every mod-`q` combination that removes `e_t` also removes `f`: `y_0 H − y_1` is the same in
     both hybrids.
   * So the information sits only in the integer noise exposed by zero tests (§2.2). LWE-type
     statements, which are mod-`q` pseudorandomness statements, reach it only through hybrids that
     keep the integer zero-test law. That is the consistency barrier again.

   **Stops.**

## 5. The fat sibling-pad lemma (PR #71) is outside these barriers

* **Only one zero child.** FSP's meeting block `B` has a zero target on the departure child only,
  `B D_dep = E`; on the chain child, `B D_chain = U` is uniform.
  * The defect statistic needs two zero children.
  * The consistency lemma is vacuous with one structured target, so preimage-first simulation of
    `D_dep` is statistically exact when `B` is hidden.
  * Neither §2.2 nor §3 applies. This agrees with PR #71's table, which has no barrier for the
    equality-cube flip.
* **Standalone form (product-LWE).** After leaf-first, a class string's continuation value is
  `z_x = c_x U + (label) + ε_x`, with:
  * `U = B D_chain` uniform and used nowhere else;
  * `c_x = σ_y τ_x` the twisted product rows;
  * `ε_x` GGH15 path noise.

  FSP holds iff the family `{c_x U + ε_x}` hides an additive common label.
  * *Independent rows.* If the rows `c_x` were independent uniform, this would be LWE with secret
    `U` and public `c_x`, and FSP would follow from LWE. That is the case `2^N ≤ n'`.
  * *Product rows.* For product rows, short (ternary, support `≈ n' log q`) affine relations
    exist by pigeonhole. Finding one is SIS on **hidden** rows, which have product structure. We
    know no method.
  * *Not CVW18.* The statement is CVW18 Lemma 7.4 in white-box form without fresh noise, i.e.
    CVW18 Cor. 5.9 with a fat root.
  * **Open, unrefuted, and not blocked by any barrier found so far.** We suggest it as the target
    for future proof attempts, ahead of `ML_i`.

## 6. Formal results of this note

* `TwoSided.decoded_defect_attack` (Lean): the exact identities of the §2.2 attack over a field.
  * If `c_t` lies in the span of the other pad rows, there is `α` with `α_t = 1`.
  * The `α`-combination of the defects `N_0 D_0^{-1} − N_1 D_1^{-1}` is `0` without the planted
    noise.
  * It is `f_0 D_0^{-1} − f_1 D_1^{-1}` with it.
* `TwoSided.two_child_preimage_consistency` (Lean): square invertible preimages `D_0, D_1` of
  targets `Y_0, Y_1` under one matrix exist iff `Y_0 D_0^{-1} = Y_1 D_1^{-1}` (§3).
* `TwoSided.decryption_recovers_noise` (Lean): if `b = ℓ + z (mod q)` with `2|z| < q`, then the
  centred lift of `b − ℓ` is `z`. A decryptor who knows the label recovers the integer noise,
  which is TLWE's attack (§4, item 2).
* No new open node. The faithful standalone statement TSR_Ψ is the existing open node
  `Reroute.multipass_subtree_hop` (with `ML_i` as its minimal form).

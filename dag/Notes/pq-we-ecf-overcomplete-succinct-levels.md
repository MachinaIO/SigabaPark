---
title: Equality-cube flip in the overcomplete case, succinct-LWE-shaped GGH15 levels, and whether the flip completes a multi-pass WE - one-child integrality test, shift dichotomy, multi-block counting
refs: [definition:WE_CircuitSAT, definition:GGH15, definition:WE_MaskedGGH15, definition:SuccinctLWE, definition:DecomposedLWE, note:pq-we-multipass-ggh15, note:pq-we-two-pass-reroute, note:pq-we-mp2-cryptanalysis, note:pq-we-plr-hop-rank-and-erase, note:pq-we-ggh15-vocabulary-open-lemmas, note:pq-we-shallow-split-arrangements, note:pq-we-hybrid-count-barrier, note:pq-we-split-lemma-attempts, note:pq-we-masked-overcomplete-leaf, theorem:AdvancedEncryption.WE.MaskedLeaf.mask_of_affine_relation, theorem:AdvancedEncryption.WE.MultiPass.no_honest_rectangle, theorem:AdvancedEncryption.WE.Reroute.multipass_subtree_hop, theorem:AdvancedEncryption.WE.Reroute.two_pass_cross_rank_le, theorem:AdvancedEncryption.WE.FlipShift.one_child_integrality, theorem:AdvancedEncryption.WE.FlipShift.succinct_slot_shift, theorem:AdvancedEncryption.WE.FlipShift.stacked_hint_decodes, theorem:AdvancedEncryption.WE.FlipShift.eq_zero_of_spanning_annihilated, theorem:AdvancedEncryption.WE.FlipShift.one_zero_child_explains, theorem:AdvancedEncryption.WE.FlipShift.multiblock_cover_card_le]
tags: [witness-encryption, ggh15, barrier, open-problem, candidate]
---
Design-AI sub-task (ff) on `Def_WE_CircuitSAT` (NAND Circuit-SAT, 128-bit witness, `2^12` gates,
`λ = κ = 128`). The efficient multi-pass candidate MP2/MP3 (`pq-we-multipass-ggh15`, about
`2^97` bits) misses one lemma. Open PRs cited by number (not merged when this note is written):
#71 (equality-cube flip, ECF, and its core, the fat sibling-pad lemma FSP), #83 (XWE, about
`2^147.7` bits), #84 (two-sided LWE: masked-leak lemma `ML_i`, decoded-defect attack, two-child
preimage consistency), #86 (TLWE at the last level of masked GGH15). The six `FlipShift` theorems
have complete Lean proofs. Everything else is an informal argument.

**Answer.**

1. **Overcomplete ECF/FSP: neither proved nor attacked; its content is sharpened (§1).**
   * The meeting block is fully explained by its zero child: `B = E_B D_dep⁻¹`
     (`one_zero_child_explains`). Every class pad is `(c_x E_B)·(D_dep⁻¹ D_chain F)`, a *short*
     row times a public matrix. So FSP is not "LWE with a uniform secret `U = B D_chain`": given the
     public preimages, `U = E_B D_dep⁻¹ D_chain`. Its only hidden data are the short correlated
     rows `s_x = c_x E_B`, which satisfy short integer relations (pigeonhole) that are hidden only
     because the twisted products `c_x` are hidden.
   * Correction to #84 §5: one decodable zero child already suffices to detect a planted hidden
     row (`one_child_integrality`, an integrality test over `Q`). FSP escapes the decoded-defect
     barrier not because it has one zero child, but because the two ECF hybrids differ by a label,
     not by a planted row. Reductions for the ECF may therefore hold trapdoors.
   * The overcomplete case is forced in MP2/MP3. Any block that protects the reroutes against
     CVW18 variable-partition tests (twisted on the first copy, zero on witnesses) is exposed in
     the class `Γ_t` by `≥ 2^{n−1}` prefixes with distinct twisted rows, against a hidden
     dimension `n' ≈ 2^{10}`.
   * No attack: every known statistic needs either zeros in `Γ_t` (none) or a common decoded
     suffix for many prefixes (multi-pass gives each prefix its own witness suffix).
2. **Succinct-LWE-shaped levels do not escape the decoded-defect barrier (§2).** The hint
   `T = [I_ℓ ⊗ B | W]⁻¹(I_ℓ ⊗ G)` gives preimages under `B` only up to a `W`-shift
   (`succinct_slot_shift`). Canonical decryption forces the shift to cancel on a spanning set of
   witness rows (`eq_zero_of_spanning_annihilated`). There are two ways to cancel it:
   * expose the `W`-part. Then `T` decodes every slot (`stacked_hint_decodes`), and a reduction
     holding `T` defeats itself (#84 §3, strengthened to one child by `one_child_integrality`);
   * use targets that already have known short `B`-preimages. That is preimage-first simulation,
     which #84's two-child consistency forbids for square levels.

   Decomposed LWE has no preimages. TLWE is decodable in every correct regime (#84; #86 uses it
   only at the mask level). **No allowed assumption supplies trapdoor-free preimages of structured
   zero targets, which is what `ML_i` needs.**
3. **The ECF does not complete an MP-type WE (§3).**
   * Label flips over fixed class maps, even additive multi-block ones, need total width
     `≥ 2^n/k` (`multiblock_cover_card_le`). So reroutes are needed.
   * In regime (d) the reroutes are fat. In regime (b) the flip is already provable and the
     reroute is `ML_i`.
   * With the ECF plus ERASE plus projection-provable reroutes, every regime needs width
     `D ≥ 2^{n/2} = 2^{64}` at the split levels. The cost is then `≥ 2^{174}` bits (the model of
     `pq-we-shallow-split-arrangements`), above XWE (`2^{147.7}`, #83) and far above the
     conditional `2^{97}` of MP2.
   * **The remaining gap for an efficient MP WE is `ML_i` (`Reroute.multipass_subtree_hop`)
     alone. It is out of reach of every reduction that simulates the witness-carrying downstream
     levels by trapdoors, succinct hints, TLWE trapdoors or preimage-first.**

## 1. Task 1: the overcomplete equality-cube flip

**Setting (#71 §2–§4).** Regime (d) places the comparator on the last copy. The class
`Γ_t = {(y, g, t)}` contains no witness when `¬φ(t)`. Leaf-first LWE climbs each equality block
`(eq, E^a_j)` up to the meeting block `B = (eq_{j−1}, E^a_j)`. Its two children are:

* the chain child, with uniform target `U = B D_chain`;
* the departure child, with target `B D_dep = E_B`. This is an encoding of zero, forced by
  witnesses in `dep_j`.

`B` is exposed by the prefix rows `c_x = j_E [y_j ≠ t_j] σ_y S'_g S'_{t<j}`, `2^{n−1+s}` of them in
`n'` dimensions.

### 1.1 The meeting block holds no hidden uniform randomness (Lean)

`one_zero_child_explains`: if `B D = E` with `D` invertible, then `B = E D⁻¹` and
`c (B D') = (c E)(D⁻¹ D')`. Consequences:

* The class pads are `c_x U F_t = (c_x E_B) H F_t`, with `H = D_dep⁻¹ D_chain`. `H` is computable
  by anyone, because the preimages are public.
* The statement "`U` uniform and used nowhere else" (#84 §5) holds marginally, in the hybrid's
  sampling, but not conditionally on the view. So FSP cannot be reduced to LWE with secret `U` and
  public `c_x`, even in principle. The case of independent rows is handled by projection (CVW18
  Lemma 4.4), not by such an LWE step.
* The secrets of FSP are the short rows `s_x = c_x E_B`. They lie in the `n'`-dimensional row
  lattice of `E_B`. By pigeonhole, short integer affine relations `Σ α_x s_x = 0` with `Σ α_x = 1`
  exist once `2^N ≳ n' log ‖c‖` (here `ℓ_1(α) ≲ 2^{40}`). Such an `α`, if known, reveals the label
  (`MaskedLeaf.mask_of_affine_relation`).
* **FSP is therefore a "hidden-relation short-secret LWE" statement.** Its whole hardness is that
  the relations among `c_x` (products of hidden twisted Gaussians) are hidden. This is
  BPR/CVW18-Lemma-7.4 hiding *without* rounding or fresh noise, white-box over `2^N` evaluations.
  No LWE-family assumption we know (plain, ring or circular LWE, succinct, decomposed, TLWE)
  states it.

### 1.2 One decodable zero child suffices for planted rows (Lean)

`one_child_integrality` works over `Q`. Let `α` be an affine relation among the prefix rows with
common denominator `Δ`. Suppose the integer noises `N_x = c_x M + e_x D` are decoded along **one**
common suffix with invertible product `D`. Then `Δ Σ α_x N_x D⁻¹` is integral. A planted hidden
row `δ` with `δ D = f` small adds `Δ f D⁻¹`, which is generically non-integral.

* A numeric check (random integer instances, `k = 4`, `m = 6`, 8 prefixes, script not in the DAG)
  separated the two cases in 289 of 295 trials. The failures were instances with `f = 0` or with
  `Δ f D⁻¹` integral by chance.
* **Consequence for `ML_i` (#84 §3).** A reduction must not be able to decode below *either*
  child for many prefixes along a common suffix. Making one branch trapdoor-free is not enough.
  Since GGH15 levels are shared by all paths, any trapdoor of any level matrix below the cut
  decodes both children anyway.
* **Consequence for the ECF.** The ECF's hybrids differ by the label `λ` (eq top rows), not by a
  planted row. `B` and its zero child occur in both. So neither the two-child statistic of #84 nor
  the one-child integrality test separates them. This is the real reason FSP escapes the barrier.
* Decoding with a downstream trapdoor yields the prefix secret rows and the noises, but not `λ`.
  `λ` sits in `A_i D_{>i}`, whose meaning depends on where the reduction embeds its challenge. So
  ECF reductions **may** hold trapdoors in the witness-free part.
* Intermediate hybrids that plant or remove a row, such as making `B`'s departure target uniform,
  are caught by the integrality test whenever the reduction decodes below the departure child.
  They are already ruled out by canonical decryption of `dep_j` witnesses (#71).

### 1.3 Overcompleteness is forced (twist versus fatness)

* FSP is provable by projection exactly when the exposure rank of the meeting block is at most its
  hidden dimension.
* Rank protection of the reroutes needs a zero-carrying block that is twisted (bit-dependent) on a
  first copy. With thin first copies the cross rank is `≤ K·t ≈ 2^{37}` (#71, `thin_cross_rank_le`);
  with twisted ones it is `≤ t^3` (`Reroute.two_pass_cross_rank_le`). The CPRF block contributes
  nothing, because it cancels in `J_O − J_C`, noise terms included.
* Such a block has a meeting block in `Γ_t` (at the last-copy level, or at a gate level for
  gate-only clauses). Every prefix `(y, g)` reaches that meeting block with a distinct twisted row.
* Hence exposure `≥ 2^{n−1} ≫ n' = 2^{10}` in every MP2/MP3 variant that keeps its reroutes
  unrefuted.
* Selective thinning does not escape this. Thinning the equality blocks and keeping the Tseitin
  blocks twisted moves the fat meeting block to the Tseitin clauses.

### 1.4 Attack attempts (all fail)

* **Rank tests.** `Γ_t` contains no zero. Witness zeros beside it give one decodable suffix per
  prefix (`MultiPass.no_honest_rectangle`). The variable-partition rank is `t^3 > 2^{64}`.
* **Integrality / decoded defect.** Needs a common decoded suffix (§1.2). Not available to the
  real adversary.
* **Witness-assisted relation learning.** The witness `w ∈ dep_j` exposes `c_{x_w} E_B` only inside
  `N(w)`, mixed with path-specific terms. One witness per prefix gives no rectangle.
* **Switching to the departure branch.** Multiplying chain values by `(H F_t)⁻¹` maps them exactly
  to the departure values `P_x D_dep`, which carry no label. So it is uninformative.
* **Rounding.** Learning with rounding; no structure survives.

**Verdict on (1).** Open, unrefuted, no barrier known. Its exact content is "hidden-relation
short-secret LWE on twisted products" (§1.1). It is not reducible to any allowed assumption by the
moves we know.

## 2. Task 2: succinct-LWE-shaped levels `[I ⊗ B | W]`

**Hint (`Def_SuccinctLWE`).** The hint `T` is public in the assumption. Its blocks satisfy
`B T_{k'k} + W_{k'} T_{W,k} = δ_{k'k} G`.

1. **Shift (`succinct_slot_shift`).** Take the level matrix `A_{i+1} = B`. The hint's preimage
   `T_k G⁻¹(Y)` of a downstream target `Y` hits `Y − W_k Z` with `Z = T_W G⁻¹(Y)` short. A level
   value `sB + e` continued through it gives `sY − (sW_k)Z + noise`. Here `sW_k` is uniform for
   every non-zero prefix row `s`, so the shift is full-size.
2. **Canonical decryption forces the shift to vanish.** By statement-independence there are
   statements whose witness prefix rows at an overcomplete cut span the row space. Then the shift
   must vanish on all of them, and `eq_zero_of_spanning_annihilated` gives `W_k Z = 0`. With `W_k`
   uniform, that is a short-kernel (SIS) condition on `W_k T_W`. Equivalently, `Y = B(T_k Z')` has
   a *known* short `B`-preimage.
3. **Dichotomy.**
   * **(a) Cancel the shift by exposing the `W`-part** `Σ s_k W_k + e_W`. Then `T` decodes every
     slot (`stacked_hint_decodes`). A reduction holding `T` (it must, to simulate) defeats itself
     by the decoded-defect statistic, which by §1.2 needs only one child. This is exactly #84's
     decoded-defect attack, checked against the redesign: **the attack applies.**
   * **(b) Choose targets with known short `B`-preimages.** This is preimage-first simulation, and
     the hint adds nothing to it. The two structured children of a square level must satisfy
     `Y_0 D_0⁻¹ = Y_1 D_1⁻¹` (#84, two-child consistency), which fails for honest targets.
     Rectangular levels shrink `m` by a factor 2 per level, which is impossible over `L = 4352`
     levels.
4. **Other hinted assumptions.**
   * Decomposed LWE gives `sᵀA_iB_j` products with public factors, depth 2, and no preimages.
   * TLWE's trapdoor decodes in every regime compatible with correctness (#84). #86 (sub-task dd)
     uses TLWE, or a plain published trapdoor, only for the mask block at the last level. Such a
     trapdoor decodes only strings whose constraint pad vanishes (witness completions), so it gives
     neither the adversary nor a reduction the common-suffix decoding of §1.2. It also supplies
     none of the downstream preimages that `ML_i` needs. This agrees with #86's finding that it
     gives no per-path handle.

**Verdict on (2).** The `W`-hint does *not* give the downstream preimages without enabling
decoding. Every way to make the shift harmless either decodes or is preimage-first.

## 3. Task 3: does the ECF complete an MP-type WE?

* **Reroutes are unavoidable even with additive multi-block labels (`multiblock_cover_card_le`).**
  Suppose the final value is a sum over blocks of class-indexed top rows, with fixed class maps
  `f_r`. A flip changes one class of one block. If every hop changes at most `k` consistent
  strings and every string changes at some hop, then `2^n ≤ k Σ_r W_r`. This generalizes #71's
  single-map lemma. More passes or more equality clauses only add blocks, which does not help.
* **Which reroutes remain.** In regime (d) (comparator on the last copy) the reroutes are fat and
  carry the consistency barrier (#71, `fat_reroute`). In regime (b) the flip is a provable
  single-prefix ERASE and the reroute is `ML_i`. So **a proof of the ECF would not reduce MP2's
  gap**: regime (b) already dominates.
* **Cost with the ECF and projection only.**
  * Projection reroutes need `D·W ≥ 2^n` at the split levels: `pq-we-multipass-ggh15` §3 regimes
    (a)–(d) and #59's fixed-cut lemma.
  * Balancing first-copy width `W` against split width `2^n/W` over `n` and `2^{12}` levels in the
    cost model of `pq-we-shallow-split-arrangements` gives `W ≈ 2^{63}` and a cost of about
    `2^{174}–2^{185}` bits. The range depends on `n'` per class.
  * At that width the thin variant is out of rank-test range (`K·t ≥ 2^{64}`). The ECF is then
    provable modulo #71's gate-chain caveat. Even so it is dominated by XWE (`2^{147.7}`, #83) and
    is only `≲ 2^{14}` below brute force (`2^{188}`).
* **Conditional MP2.** MP2's `2^{97}` (`d ≈ 2^{23.6}`, `m ≈ 2^{40}`, `log q ≈ 2^{16.5}`,
  `L = 4352`, premises of about 400 bits for `≈ 2^{136}` hops) still needs `ML_i` for all
  `2(n − j)` merges per threshold.

## 4. Exact remaining gap

* **`ML_i` / `AdvancedEncryption.WE.Reroute.multipass_subtree_hop`**, the only missing lemma of an
  efficient MP WE. Necessary property of any proof, from #84 §3 together with
  `one_child_integrality`: the reduction simulates the witness-carrying downstream levels with
  *no* ability to decode any branch along a common suffix. Trapdoors, succinct hints (§2), TLWE
  trapdoors and preimage-first all violate this.
* **New assumption type needed.** A standard-form, statement-independent assumption whose
  instances contain GGH15-type preimages of *structured* zero targets without decodability. None of
  the allowed assumptions has this. Evasive LWE postulates it and is excluded. The open question
  is whether such an assumption can be stated falsifiably and checked against the integrality
  test of §1.2.
* **ECF / FSP** (#71): open. It is now precisely "hidden-relation short-secret LWE on twisted
  products" (§1.1), with no barrier. It is not on the critical path, because §3 shows that a proof
  of it does not give a WE cheaper than `2^{174}`.

## 5. Formal results (complete proofs)

* `FlipShift.one_child_integrality`: integrality test with one decodable child (§1.2).
* `FlipShift.one_zero_child_explains`: `B D = E` implies `B = E D⁻¹` and pads equal a short row
  times a public matrix (§1.1).
* `FlipShift.succinct_slot_shift`: the hint's `W`-shift (§2).
* `FlipShift.stacked_hint_decodes`: `T` decodes stacked samples (§2).
* `FlipShift.eq_zero_of_spanning_annihilated`: shifts vanishing on a spanning set vanish (§2).
* `FlipShift.multiblock_cover_card_le`: `|X| ≤ k Σ W_r` for multi-block flips (§3).

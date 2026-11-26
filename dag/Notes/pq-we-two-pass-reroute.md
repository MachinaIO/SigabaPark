---
title: The two-pass reroute lemma of multi-pass masked GGH15 WE - reduction to one hidden row per chain level, four failed proof attempts, a consistency barrier and pass-count sensitivity
refs: [definition:WE_CircuitSAT, definition:GGH15, definition:WE_MaskedGGH15, note:pq-we-ggh15-vocabulary-open-lemmas, note:pq-we-plr-hop-rank-and-erase, note:pq-we-split-lemma-attempts, note:pq-we-masked-evaluator-mechanisms, note:pq-we-hybrid-count-barrier, note:we-circuitsat-bruteforce-explicit-cost, theorem:AdvancedEncryption.WE.Split.preimage_congr, theorem:AdvancedEncryption.WE.Split.preimage_correlated_copy, theorem:AdvancedEncryption.WE.Split.preimage_row_transform, theorem:AdvancedEncryption.WE.Hybrid.hardAt_chain, theorem:AdvancedEncryption.WE.Gray.adjacent_one_bit, theorem:AdvancedEncryption.WE.MaskedGGH15.plr_hop, theorem:AdvancedEncryption.WE.Reroute.adjacent_chains_redundant, theorem:AdvancedEncryption.WE.Reroute.kilian_relations_iff, theorem:AdvancedEncryption.WE.Reroute.kilian_partition_iff, theorem:AdvancedEncryption.WE.Reroute.comparator_span_finrank_le, theorem:AdvancedEncryption.WE.Reroute.two_pass_cross_rank_le, theorem:AdvancedEncryption.WE.Reroute.multipass_subtree_hop]
tags: [witness-encryption, ggh15, candidate, barrier, open-problem]
---
Design-AI sub-task (u) on `Def_WE_CircuitSAT` (128-bit witnesses, NAND circuits with `2^12`
gates, `λ = κ = 128`). Open PR #60 (note "pq-we-multipass-ggh15", not merged when this note is
written, so cited by number) proposes the multi-pass masked γ⊗-GGH15 candidate MP2/MP3. It reduces
its security to one missing lemma, the **two-pass reroute lemma**: `H_t^{done}` (threshold `t`
after ERASE) is LWE-indistinguishable from the honest encoding at threshold `t+1`. This note
records an attempt to prove it.

The five `Reroute.*` theorems marked "Lean" have complete proofs. `multipass_subtree_hop` is an
open node. Everything else is an informal argument. CVW18 is Chen–Vaikuntanathan–Wee, ePrint
2018/360, read from the full text (Lemmas 4.1 and 4.4, Theorem 5.7 and its proof, §9).

**Answer.**

* **Not proved, and no proof is possible inside the CVW18 toolbox.**
* **Exact reduction (§1–§2).** Up to provable ERASE hops, the reroute is two collapses of
  *redundant single-prefix chains* onto a common automaton. Each collapse is a sequence of
  one-level merges. After a provable root-first projection, each merge is a statement about
  **one hidden uniform row** `δ_i ∈ Z_q^{1×m}`, which is used on both sides:
  * as a zero row of the next level's preimages (`δ_i D_{i+1,b} ≈ 0`);
  * as an additive leak into the single chain prefix's value.

  The two hybrids differ only in noise terms of every evaluation.
* **The four suggested ideas stop at precise points (§3–§5).**
  1. Kilian re-randomization preserves state partitions (Lean).
  2. Pass-2 rows cannot be borrowed: no row is hidden at any overcomplete cut, and chain pads
     inherit the departure obstruction.
  3. Leaf-first and root-first LWE stop at the first departure from the chain.
  4. CVW18 Cor. 5.9 needs the CPRF block, which the WE's two left vectors cancel on every string.
* **Consistency barrier (§4).** On true statements with two witnesses below the chain, every
  CVW18 LWE move on `δ_i` changes one witness's decrypted value and not the other's. Statistical
  moves cannot change the law of `δ_i`. So a proof needs a new **two-sided ("bilinear") LWE
  statement**.
* **Pass-count sensitivity (§6).** For `c = 2` and large `n` the lemma is (heuristically) false,
  by CVW18 Claim 9.8 and the rank bound `t^{2c−1}` (Lean, `c = 2`). A proof must therefore use a
  hypothesis such as `rows^{2c−1} ≥ 2^{n/2}`. Every known GGH15 LWE step is layout-oblivious and
  cannot use such a hypothesis.
* **Remaining gap (§7).** The lemma is stated as the open node `multipass_subtree_hop` in #57's
  vocabulary, and in its minimal form as the **masked-leak lemma `ML_i`**.

## 0. Setting (PR #60 §4)

* **Levels.** Pass 1 reads `z¹ = w_1..w_n`, pass 2 reads `z²`, and so on; then come the `2^12`
  Tseitin gate levels.
* **Secrets.** `diag(P_{i,b} ⊗ R_i, M_{i,b} ⊗ S'_{i,b}, S_{i,b})`.
  * `P` is the reflected-Gray comparator on pass 1 (states lt / eq / gt) and the identity
    afterwards.
  * `R_i` is bit-independent (#56 §2).
  * `M` is the CNF BP of `Tseitin(φ)` together with the equality clauses between copies.
* **Left matrices and labels.** Two left matrices `J_O`, `J_C`; the CPRF block cancels in
  `J_O − J_C`. The top comparator rows are `mask'` on lt and `mask` on eq/gt.
* **Values.** After CVW18 phase 1, a string `z` evaluates to
  `ρ_* · top_{κ(z¹)} − s'_0 S'_z a_{F(z)} + noise`, where `ρ_* = r_0 R_*` and `F(z)` is the set of
  clauses that `z` falsifies. Witnesses give `ρ_* mask'` (lt) or `ρ_* mask` (eq/gt).

## 1. Exact form: two redundant-chain collapses

Let `t` and `t+1` first differ at pass-1 level `j` (`AdvancedEncryption.WE.Gray.adjacent_one_bit`).
Let `I` be the set of ranks below the prefix `t_{≤j}`, and `J` the set below `(t+1)_{≤j}`. Gray
subtrees are intervals, so by `AdvancedEncryption.WE.Reroute.adjacent_chains_redundant` (Lean):

* every rank in `I` is `≤ t`;
* every rank in `J` is `≥ t+1`.

Hence:

* **`A_t`.** The honest threshold-`t` encoding whose eq top rows equal the lt top rows (`mask'`).
  In it the eq chain from level `j` to `n` sits inside a subtree that is labelled lt throughout:
  every departure goes to lt, and the end is lt-labelled. `H_t^{done} ≈ A_t` by ERASE (#56 §3, PR
  #60 §4 step 1), run with label `mask'`. Path `t` and its whole pass-2 subtree are non-witnesses,
  so this is provable at polynomial width.
* **`B_{t+1}`.** The honest threshold-`(t+1)` encoding. Its eq chain from level `j` sits inside a
  subtree labelled `mask` throughout (departures go to gt, and eq is labelled `mask`).
* **`K_t`.** The common collapse. From `eq_{j−1}`, bit `t_j` goes to lt and bit `¬t_j` goes to gt;
  the eq rows below level `j` are unreachable.

`A_t`, `K_t` and `B_{t+1}` give the same label to all `2^L` strings, as PR #60 says. Moreover:

> **Reroute = RCC_lt(A_t → K_t) followed by RCC_gt(K_t → B_{t+1})^{-1},**

where **RCC** ("redundant-chain collapse") merges a chain state that only one prefix reaches into
the absorbing state that already has all of its labels. Each RCC is `n − j` one-level hops
`SPM_i` (single-prefix merge), from `i = n` down to `j+1`:

* **`G_{i+1}`.** The chain runs `eq_j … eq_i`, and `eq_i` goes to lt on both bits.
* **`G_i`.** `eq_{i−1}` goes to lt on bit `t_i`.

In the effective rows of §2:

* **Lt rows.** `ℓ^{lt}_i D_{i+1,b} = ℓ^{lt}_{i+1} + e` for both bits.
* **Eq rows in `G_{i+1}`.** `ℓ^{eq}_i D_{i+1,b} = ℓ^{lt}_{i+1} + e'`: the same secret `R_{i+1}`,
  the same target matrix, independent noise.
* **Into `eq_i`.** `ℓ^{eq}_{i−1} D_{i,t_i} = ℓ^{eq}_i + e''`.

`SPM_i` is the multi-pass, reverse-direction form of #49's single-prefix split. Two differences
matter. The copy shares the original's *secrets* (`R` is bit- and state-independent). And its
continuation is *functionally identical*: on every suffix `u`, `(A^{eq}_i − A^{lt}_i) D_u` is
noise only.

## 2. Root-first projection and the one-row core

* **Projection lemma (PL).** This is #49 §7(iii), CVW18 Lemma 4.4 with public rows. Applied root
  first, it replaces each `D_{i+1,b}` by a Gaussian conditioned on the projections of the rows
  that the prefixes reach at cut `i`. The induction is always valid. It only stops simplifying
  where those rows span everything.
* **Scalar-row model.** The comparator part of every prefix row at cut `i` is `e_{κ(x)} ⊗ ρ_i`,
  with one common `ρ_i = r_0 R_{≤i}`. So the comparator block exposes at most 3 directions
  (`AdvancedEncryption.WE.Reroute.comparator_span_finrank_le`, Lean). These are the rows
  `ℓ^s_i := ρ_i A^s_i`. The other `3(d_R − 1)` comparator rows are hidden and are dropped by PL.
  The constraint rows `A^{con}_i` are fully visible: there are `2^i` prefixes in `w n'`
  dimensions (overcomplete).
* **One-row core.** Put `δ_i := ℓ^{eq}_i − ℓ^{lt}_i`. It is a uniform `1 × m` row. In `G_{i+1}`:
  * **(a)** the chain prefix's level-`i` target contains `ℓ^{lt}_i + δ_i`. Through the root, the
    adversary obtains `v_t = W D_{t≤i} = ℓ^{lt}_i + δ_i + c_{t≤i} A^{con}_i + e`, where `c_x` is the
    constraint row of prefix `x`;
  * **(b)** `δ_i D_{i+1,b} = e' − e`, which is small, for both `b`.
* **Noisy copy.** `G'`: `A^{eq}_i := A^{lt}_i + F` with `F` short, and eq targets *defined* as
  `R_{i+1}A^{lt}_{i+1} + E + F D`. By `preimage_congr` and `preimage_correlated_copy` (Lean,
  merged) the eq constraint is then implied, and noise flooding absorbs `R_i F` into the incoming
  target. So `G' ≈_s G_i`.
* **Core statement.** `SPM_i` is exactly **"uniform `δ_i` (independent noise) ≈ short `δ_i`
  (correlated noise)"**, for a row used as in (a) and (b).
* **The two sides differ only in noise.**
  * For every suffix `u`, `v_t D_u` in `G_{i+1}` equals the `G_i` value plus `δ_i D_u`. The latter
    is a GGH15 noise term (`e_b D_{>i+1}`).
  * On a witness `w` below the chain, the zero's noise polynomial has, in `G_{i+1}`, the
    independent term `ρ_i E^{eq}_{i+1}D_{>i+1}`. In `G_i` it has the term `ρ_i E^{lt}_{i+1}D_{>i+1}`,
    which it shares with every lt prefix.
  * In one pass, this extra independent direction is #56 §1's rank jump: a rectangle of
    witnesses across cut `i` sees it.
  * In two passes, `no_honest_rectangle` (PR #60) removes single-cut rectangles. Only
    variable-partition tests (§6) remain.

## 3. Idea (1): Kilian / statistical re-randomization of level secrets

* **Linear re-randomizations.** If two hybrids are related by invertible `T_i` on the rows
  (`X^B_x = X^A_x T_i`, with the secret laws preserved), then the linear relations among prefix
  rows are identical (`kilian_relations_iff`, Lean). For the comparator block this means the
  state partitions are identical (`kilian_partition_iff`, Lean).
* **Why the reroute is not of this form.** At every level `i ∈ [j, n]`, `A_t` separates
  `t_{≤i}` (eq) from the other lt prefixes, and `K_t` merges them. So no Kilian map exists, at any
  width or dimension, overcomplete or not.
* **Adding blocks.** Mixing in the constraint or CPRF blocks does not help. The relation space of
  the joint rows is the intersection of the relation spaces of the blocks. Since `2^i ≫ D`, it
  contains a relation with a non-zero coefficient on `t_{≤i}` that is balanced for the `K_t`
  partition but not for the `A_t` partition.
* **Statistical arguments.** None works. An unbounded adversary finds `δ_i` as a short-noise left
  kernel vector of `D_{i+1,b}` (an LWE/SIS search), so `G_{i+1}` and `G_i` are statistically far.
* **Stops:** the reroute changes an invariant of every invertible re-randomization. A
  computational step must touch `δ_i`.

## 4. Idea (3): LWE hybrids (leaf-first at pass-2 levels, root-first), and a consistency barrier

* **Leaf-first (CVW18 Lemma 5.10 style).** With the eq top rows set to a fresh `mask''` (allowed
  after ERASE), the eq rows at the levels after pass 1 have a unique source and no zeros. LWE with
  secret `A^{eq}_i` and public `R_i` turns their targets uniform. Lemma 4.1 then drops the rows,
  down to the end of pass 1. This is ERASE again.
  * At chain level `i ≤ n` the eq row of `A_{i−1}` has two targets: `R_i A^{eq}_i + E` (bit
    `t_i`) and `R_i A^{lt}_i + E` (bit `¬t_i`, the departure).
  * The second is shared with the lt class, so it is never uniform, and Lemma 4.1 cannot drop the
    row.
  * **Stops at the first departure.**
* **Root-first (Lemma 4.4 / PL).** The chain prefix row is reached from the root `W`, so
  `D_{t≤i}` is never Gaussian. **Stops at the chain prefix (§2).**
* **The departure obstruction is forced (consistency barrier).** Take a true statement with two
  witnesses `w, w'` below `t_{≤j}`, where:
  * `w` passes through `eq_i` and departs at level `i+1`;
  * `w'` departs earlier.

  Both values equal `ρ_* mask'` in `A_t` (up to noise), and a decryptor holding both checks this.
  The hop must hold on such statements, because `t` is a non-witness and the hop is
  statement-independent.
  * A CVW18 LWE move on `δ_i` replaces one side by uniform:
    * replacing the incoming target (a) adds `U D_{>i}` to `w`'s value only;
    * replacing the zero-row target (b) adds `U D_{>i+1}` to the strings through `eq_i`, again
      `w` but not `w'`.
  * Each such hybrid is distinguished with advantage about 1.
  * Statistical moves cannot change the law of `δ_i` (§3).
  * The same holds for any other block whose change would make `δ_i` one-sided: its departing
    witness values tie it in the same way.

  **So no sequence of CVW18 moves (Lemmas 3.9, 4.1, 4.4, PL, flooding, row transforms) proves
  `SPM_i`.** A proof needs a computational step that keeps `δ_i` two-sided. In other words, an
  LWE-type statement for a secret that is used both as a left factor (target `R_i δ_i`) and as a
  right factor (zero row of `D_{i+1}`), which is exactly the bilinear form that #49 §4(2a) found
  is not LWE.
* **Not a contradiction with the hybrid-count barrier.** The obstruction is per hop: it is the
  witness-pair consistency, not the number of hops.

## 5. Ideas (2) and (4)

**(2) Borrowing rows from pass-2 levels.**

* The merge needs a pad for `δ_i` that hides it in `v_t` but is cancelled on witness completions.
  The only available pad is `c_{t≤i} A^{con}_i`, and witness completions annihilate it. It is not
  a one-time pad, because `A^{con}_i` is fully visible.
* At any cut beyond `log₂ D`, the visible rows span the whole row space (`2^i` prefixes in pass 1,
  `2^{n+i}` in pass 2). **No hidden row exists anywhere to borrow**: more passes only add
  prefixes.
* A dedicated *chain-pad block* (extra rows carried only by `eq`) must vanish at every departure,
  or departing witnesses lose canonical decryption. Its rows then have zero targets on departure
  bits, so it inherits the departure obstruction of §4.
* Equality clauses do not help either. A permutation-BP equality check
  `σ(z¹)σ(z²)^{-1}` (with pass 2 read in reverse) has small width and no zeros, which is where
  GKW17 and WZ17's leaf-first proofs work. But it does not vanish on witnesses, so the masked
  cancellation needs the CNF (diagonal, zero-producing) form, and leaf-first fails on its zero
  rows.
* **Stops.**

**(4) CVW18 Cor. 5.9 on a jointly read program.**

* Cor. 5.9 is a whole-encoding statement given `J·A_0` with `J = (J' | I_n)`. Its proof (Lemmas
  5.10 and 5.11) needs the `S` (CPRF) rows as a per-path pad. The WE publishes both `J_O A_0` and
  `J_C A_0`, whose difference cancels that block on every string. After phase 1 strips it, we are
  in the Remark 5.8 situation (a root row without `I_n`), where the corollary is false in general.
* Reading two passes "jointly" as one read-once program needs paired levels. Pairing copy `k` of
  pass 1 with copy `k` of pass 2 (an interleaved or dual-input layout, as in BGMZ18) recreates
  honest rectangles at every cut, which is exactly what passes are for.
* **Stops.**

## 6. Pass-count sensitivity: what any proof must use

* **Rank bound.** By `AdvancedEncryption.WE.Reroute.two_pass_cross_rank_le` (Lean), for any
  partition `X | Y` of the witness variables, the `X × Y` matrix of two-pass products
  `u P₁(x) Q₁(y) P₂(x) Q₂(y) v` has rank `≤ t^3`. With `c` passes the same factorization gives
  `t^{2c−1}`.
* **The attack.** When `t^{2c−1} < 2^{n/2}`, honest-zero matrices over a balanced partition are
  rank-deficient. CVW18 Claim 9.8 then distinguishes functionally equivalent `c`-repeating
  programs.
* **The reroute is of this kind.** `A_t` and `B_{t+1}` (or `G_{i+1}` and `G_i`) are equivalent
  programs whose noise structures differ by one independent direction (§2). So for fixed `c`
  and large `n` the lemma is expected to be **false** (PR #60's caution).
* **Consequence for proofs.** A correct proof must use a hypothesis that fails for `c = 2` at
  large `n`, such as `rows^{2c−1} ≥ 2^{n/2}`.
  * Every GGH15 LWE step known to us is layout-oblivious: CVW18 Thm 5.7 and §7, the GKW17 / WZ17
    lockable-obfuscation proofs, and BGMZ18's LWE part. It never reads `var`, so it cannot use
    such a hypothesis.
  * **So the lemma is beyond those techniques for a structural reason, not only for lack of a
    trick.**
  * The only frameworks we know that are sensitive in this way are model-based (BGMZ18's GGH15
    zeroizing model under the bounded-speedup hypothesis). They are not LWE.
* At `n = 128` the hypothesis holds for MP2 (`2^{23.6·3} > 2^{64}`) and MP3.

## 7. Remaining gap, stated precisely

**Open node (in #57's vocabulary): `AdvancedEncryption.WE.Reroute.multipass_subtree_hop`.**

* **Scheme.** `positionalView` over `h` levels whose first `c·n` levels are `c ≥ 2` copies of the
  witness, with `Ψ` containing the equality clauses between consecutive copies.
* **Threshold.** `T = t·2^{h−n}`. The comparator reads all levels. Its labels are "pass-1 rank
  `< t`", and the chain continues as a redundant chain below the codeword of rank `t`. This is
  label-equivalent to PR #60's comparator, which is the identity after pass 1.
* **Hypotheses.** `rows^{2(2c−1)} ≥ 2^n`, and no string with pass-1 copy equal to codeword `t`
  satisfies `Ψ` (that is, `¬φ(t)`).
* **Claim.** `T → T + 2^{h−n}` is `CloseAt` with loss `(h+1)·hopLoss(h, rows)` under decision LWE.
* **Content.** One ERASE plus the two-pass reroute (§1). Chained by `hardAt_chain` over `2^n`
  thresholds, it gives the WE walk. The hop count is the one allowed by
  `pq-we-hybrid-count-barrier`.
* **Caveat.** #56's ERASE proof uses per-class constraint blocks, which `positionalView` does not
  have. So the node also asks for ERASE in this exact scheme. A per-class variant would need its
  own definition node.

**Minimal form, `ML_i` (masked-leak lemma).** Work in the scalar-row model after PL. Let `δ` be a
hidden uniform row planted as a zero row of `D_{i+1,b}` (`δ D_{i+1,b} = e_b`). Then the view in
which the chain prefix's value is leaked as

`v_t = ℓ^{lt}_i + δ + c_{t≤i} A^{con}_i + e`

is indistinguishable from the same view with `δ` removed from `v_t`. Indeed:

* "planted but not leaked" `≈ G_i`, by PL, since `δ` is then one-sided;
* "leaked" `= G_{i+1}`;
* so `RCC = ∏_i ML_i`, and the reroute is `2(n − j)` instances of `ML_i`.

`ML_i` is:

* **false** in one pass (#56 §1 rank jump);
* expected **false** for `c = 2`, `n → ∞` (§6);
* **unrefuted** at `n = 128` for `c ≥ 2`;
* outside the CVW18 toolbox (§4);
* the reverse of #49's single-prefix split, now with shared secrets and an identical continuation.

**Regime (d) lemma of PR #60 (equality-cube flip).**

* It flips, in one hop, all strings `(z¹, w)` whose last copy is a non-witness `w`. All of them
  lie below the end-of-pass-2 eq node, which `2^n` prefixes reach (a fat class).
* Leaf-first LWE works on its `(eq, E_k)` blocks: below that node there are no zeros and each
  block has a unique source.
* The ERASE pad step then needs the class rows to be independent, which they are not (`2^n`
  prefixes). This is #49 §7(v)'s **overcomplete projection lemma**, here for a class **with no
  witness below it**.
* Neither §4's consistency barrier nor #49 §6's SZK argument applies to it, because no
  decryption passes through the flipped node. So this zero-free overcomplete projection is
  strictly weaker than `ML_i`.
* We regard it as the most promising remaining target. PR #60 notes that regime (d) also needs
  fat-class splits.

## 8. Formal results of this note

* `Reroute.adjacent_chains_redundant` (Lean): both chains of a reroute are redundant (§1).
* `Reroute.kilian_relations_iff` (Lean): invertible re-randomization preserves the relations among
  prefix rows (§3).
* `Reroute.kilian_partition_iff` (Lean): it preserves comparator state partitions (§3).
* `Reroute.comparator_span_finrank_le` (Lean): the comparator exposes one direction per state,
  which gives the scalar-row model (§2).
* `Reroute.two_pass_cross_rank_le` (Lean): the cross-partition rank of two-pass products is at
  most `t^3` (§6).
* `Reroute.multipass_subtree_hop` (open): the per-threshold hop of the multi-pass walk (§7).

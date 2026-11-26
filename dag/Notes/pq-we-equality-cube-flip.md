---
title: The equality-cube flip of multi-pass masked GGH15 WE (regime (d)) - exact statement, fat sibling-pad core, a thin variant, and why reroutes remain
refs: [definition:WE_CircuitSAT, definition:GGH15, definition:WE_MaskedGGH15, definition:WE_LastPassGGH15, note:pq-we-multipass-ggh15, note:pq-we-split-lemma-attempts, note:pq-we-masked-overcomplete-leaf, note:pq-we-plr-hop-rank-and-erase, note:pq-we-ggh15-vocabulary-open-lemmas, note:pq-we-hybrid-count-barrier, note:pq-we-shallow-split-arrangements, note:we-circuitsat-bruteforce-explicit-cost, theorem:AdvancedEncryption.WE.MaskedLeaf.hiding_of_separator, theorem:AdvancedEncryption.WE.MaskedLeaf.mask_of_affine_relation, theorem:AdvancedEncryption.WE.MaskedLeaf.separator_iff_no_affine_relation, theorem:AdvancedEncryption.WE.MaskedLeaf.untwisted_separator_iff, theorem:AdvancedEncryption.WE.MultiPass.no_honest_rectangle, theorem:AdvancedEncryption.WE.Split.preimage_correlated_copy, theorem:AdvancedEncryption.WE.Hybrid.hardAt_chain, theorem:AdvancedEncryption.WE.LastPass.equality_cube_flip, theorem:AdvancedEncryption.WE.LastPass.fat_reroute, theorem:AdvancedEncryption.WE.LastPass.lastpass_walk, theorem:AdvancedEncryption.WE.LastPass.card_le_width_mul_of_fixed_partition, theorem:AdvancedEncryption.WE.LastPass.exists_unique_first_mismatch, theorem:AdvancedEncryption.WE.LastPass.thin_cross_rank_le, theorem:AdvancedEncryption.WE.LastPass.not_sat_of_copies_differ, theorem:AdvancedEncryption.WE.LastPass.departure_kills_chain_clause]
tags: [witness-encryption, ggh15, candidate, barrier, open-problem]
---
Design-AI sub-task (w) on `Def_WE_CircuitSAT` (128-bit witnesses, NAND circuits with `2^12`
gates, `λ = κ = 128`). `pq-we-multipass-ggh15` (PR #60, §3(d)) names a second open hop type for
the multi-pass candidates MP2/MP3, the **equality-cube flip** (ECF). In one hop it flips the
consistent string `w^c` together with all orphan mixed strings `(y, …, w)`, which are certified
by the equality clauses. Open PR #61 (note "pq-we-two-pass-reroute", not merged when this note is
written, so cited by number) reduces the ECF to #49's overcomplete projection lemma on a class
with no witness below. It observes that neither its consistency barrier nor #49's SZK barrier
applies, and calls the ECF the most promising target. This note attacks it.

Lean nodes of this PR:

* definition `WE_LastPassGGH15`;
* two **open** theorem nodes, `equality_cube_flip` and `fat_reroute`;
* a **sketch** `lastpass_walk`, which proves the whole regime-(d) walk from the two open nodes;
* five exact lemmas with complete proofs (§8).

Everything else is an informal argument. CVW18 is Chen–Vaikuntanathan–Wee, ePrint 2018/360,
read from the full text (Lemmas 3.9, 4.1, 4.4, Theorem 5.7 with Lemmas 5.10/5.11, Theorem 7.5
with Lemmas 7.4/7.7).

**Answer.**

1. **Statement (§1).** The ECF is stated exactly as the open node
   `AdvancedEncryption.WE.LastPass.equality_cube_flip`. The scheme is `lastPassView`: masked
   γ⊗-GGH15, with `c ≥ 2` witness copies, equality clauses between consecutive copies, and the
   comparator on the *last* copy. The hop flips the eq-leaf label from `mask` to `mask'`, under
   the local hypothesis that no string whose last copy is codeword `t` satisfies `Ψ`. By
   `not_sat_of_copies_differ` (Lean) that hypothesis reduces to `¬φ(t)`.
2. **Barriers.** The "no witness below" condition removes every barrier known in the DAG:
   * the witness-pair consistency barrier (PR #61 §4);
   * the SZK barrier (#49 §6);
   * the rank-jump and pass-count obstructions (#56 §1, PR #61 §6), because the flip changes a
     label on a fixed class structure;
   * the hybrid-count barrier, because the hop is local.

   So **no known barrier excludes an LWE proof of the ECF** (§3).
3. **Not proved (§2, §4).** Leaf-first LWE inside the class (CVW18 Lemma 3.9 / 4.1) works
   wherever no zero exists. With per-departure classes, it climbs each equality-clause block up
   to that clause's last-copy level `j`. There it meets a **fat, two-sided block**:
   * it is exposed by all `2^{(c−1)n+s}` prefixes;
   * its chain target is uniform;
   * its departure target is an encoding of zero, forced by canonical decryption of witnesses in
     the *sibling* class (`departure_kills_chain_clause`, Lean).

   Three toolbox obstructions remain: projection is vacuous, the block cannot be made one-sided,
   and the leaf dichotomy forbids a statistical end step. The exact remaining core is the
   **fat sibling-pad lemma** (FSP, §4): GGH15 noise must hide the exact affine relations among
   `2^{(c−1)n+s}` product-structured pads.
4. **Thin variant (§6).** With bit-independent constraint secrets on the first copies, the class
   becomes algebraically thin. The ECF then reduces to the flip of the single consistent string,
   which is provable modulo a gate-chain structure. But the cross-partition rank of honest zeros
   collapses from `t^3` to `K·t` (`thin_cross_rank_le`, Lean). That is about `2^{37}` at
   `n = 128`, which re-enables CVW18's variable-partition tests against every reroute. The
   fatness that blocks the ECF proof is the same twisting that protects the reroutes.
5. **Regime (d) is not a complete proof (§5).**
   * Reroutes cannot be avoided. A walk of label flips over a fixed class map needs
     `W·k ≥ 2^n` (`card_le_width_mul_of_fixed_partition`, Lean).
   * The reroute of regime (d) is fat: its chain classes on the last copy have witnesses below
     them, so PR #61's consistency barrier applies to it.
   * The sketch `lastpass_walk` (Lean) shows that ECF + fat reroute give the whole walk, at about
     `2^{97}` bits (≈ `2^{106}` with per-departure classes).
   * Regime (d) replaces regime (b)'s *provable* single-prefix ERASE with the open ECF and keeps
     an equally hard reroute. **As a proof strategy, regime (d) is dominated by regime (b).**

## 0. Setting

* **Layout.** `c` copies of the `n = 128` witness bits, laid out as follows (`copyOff`):
  * copies `0, …, c−2` at levels `p·n, …, p·n + n − 1`;
  * then the `s = 2^12` Tseitin gate bits;
  * then the last copy at the last `n` levels.

  For MP2 `c = 2` and `h = 2n + s = 4352`; for MP3 `c = 3`.
* **CNF.** `Ψ` contains `Tseitin(φ)`, whose input literals come from the last copy, and the
  `2n(c−1)` equality clauses `(z^p_i ∨ ¬z^{p+1}_i)`, `(¬z^p_i ∨ z^{p+1}_i)`.
* **Secrets** (`Def_WE_MaskedGGH15`): `Ŝ_{i,b} = diag(P_{i,b} ⊗ R_i, M_{i,b} ⊗ S'_{i,b}, S_{i,b})`,
  with bit-independent `R_i` and twisted (bit-dependent) `S'_{i,b}`.
* **Left matrices** `J_O`, `J_C`, with a rank-one difference.
* **Regime (d) comparator** (`cmpMatFrom h (h−n) t`): the identity on every level before the last
  copy, then the reflected-Gray comparator against `t` on the last copy. Labels: `mask'` iff the
  Gray rank of the last copy is `< t`.
  * All `2^{h−n}` prefixes reach the comparator's start, so every comparator class is *fat*.
  * The **class** `Γ_t` is the set of strings whose last copy is the codeword of rank `t`, i.e.
    the strings ending in the eq leaf.
* **Cubes** (`exists_unique_first_mismatch`, Lean). For `c = 2`, a string of `Γ_t` is
  `(y, g, t)`:
  * `y = t` is the consistent string;
  * otherwise `y` has a unique first mismatch `j` and lies in the cube
    `C_j = t_{<j}·¬t_j·{0,1}^{n−j−1}`, of size `2^{n−j−1}`.

  For MP3 the cubes are taken over the pair of earlier copies.
* **The orphans' falsified clauses.** Over the class, `(y, g, t)` falsifies:
  * the equality clause `E^a_j` for **every** mismatch `j ∈ Δ(y) = {j : y_j ≠ t_j}`, not only
    the first. `E^a_j` is the clause of the pair not satisfied by `z^2_j = t_j`;
  * the Tseitin clauses `F(g, t)`, which do not depend on `y`.

  Hence:
  * **no string of `Γ_t` is a zero**, given `¬φ(t)` and `not_sat_of_copies_differ`;
  * **the consistent string carries no equality pad** (`Δ(t) = ∅`).

## 1. Exact statement

`AdvancedEncryption.WE.LastPass.equality_cube_flip` (open). Hypotheses:

* `lastPassView p h sh Ψ r0 jC s0 (h−n) t eqFlip`, with `2 ≤ c`, `c·n ≤ h`;
* the equality clauses `hEq` (laid out by `copyOff`);
* `t < 2^n`;
* `hnw`: every `z` whose last copy is `grayCode n t` falsifies `Ψ`;
* the CVW18 regime and `LWE.decision.HardAt pL k`.

Claim: `CloseAt (… t false) (… t true) k ((h+1)·hopLoss(h, rows)) simCost`.

* The two hybrids differ **only in the eq comparator rows of the top matrix** (`mask` vs
  `mask'`). The class structure is the same.
* The comparator is the honest shared lt/eq/gt block, as in `positionalView`, so the statement is
  about the real scheme.
* The proof attempt below uses #56's per-class constraint blocks, here per *departure* class.
  A proof in that variant would need its own definition node, the same caveat as PR #61 §7.

## 2. Leaf-first inside the class: how far it gets

We use #56 §3's tools: CVW18 phase 1 strips the CPRF block; Lemma 3.9 does LWE on a block with
a unique source and public short `S'_{i,0}`, `S'_{i,1}`; Lemma 4.1 drops a row block whose
targets are all uniform. The class structure on the last copy is the eq chain `eq_0 … eq_n`
together with **per-departure classes** `dep_ℓ` (the strings that leave the chain at last-copy
level `ℓ`), each absorbing. Shared lt/gt blocks give a block two sources with the same public
matrix, which is not LWE (#56 §3). Per-departure classes give every block a unique source per
bit.

* **Equality blocks `(C, E^a_j)`.** Below last-copy level `j`, clause `E^a_j` has no variable
  left, so its diagonal entry is `1` in every class: no zeros. Leaf-first runs from the leaf up
  through:
  * `eq_ℓ` for `ℓ ≥ j`;
  * every `dep_ℓ` with `ℓ > j`.

  At level `ℓ > j` the eq-chain block `(eq_{ℓ−1}, E^a_j)` has two targets, both uniform:
  `(eq_ℓ, E^a_j)` and `(dep_ℓ, E^a_j)`. So it is dropped. The climb stops at **`(eq_{j−1}, E^a_j)`**:
  * its chain target (bit `t_j`) is uniform, `U^{(j)}`;
  * its departure target (bit `¬t_j`) is `E`, an encoding of zero, because the departing bit
    satisfies `E^a_j` (`departure_kills_chain_clause`, Lean).
* **Tseitin blocks.**
  * A clause `k` with input literals in the last copy: the climb stops at the level of its
    deepest last-copy literal (same mechanism).
  * A gate-only clause: the climb passes the whole last copy, since both targets out of the start
    class are uniform, and stops at its deepest gate variable.
* **The comparator eq rows** are never switched. `R_i` is bit-independent, so on absorbing rows
  `D_{i,0} − D_{i,1}` annihilates them (#57 §5). The label is hidden, if at all, by the pads.

**The departure zero is forced, not an artefact.**

* A consistent string `w` with `w_{<j} = t_{<j}` and `w_j ≠ t_j` lies in `dep_j`.
* Its prefix at `eq_{j−1}` has a **non-zero** `E^a_j` row, since `y_j = w_j ≠ t_j` in the first
  copy.
* If the departure target were not an encoding of zero, `w`'s value would carry a pad, and
  canonical decryption would fail on statements with that witness.
* So **"no witness below" the flipped leaf does not mean "no witness beside" it.** The meeting
  block has a sibling that carries witnesses.

**What is left at the meeting block `B_j := (eq_{j−1}, E^a_j)`** (rows of the level matrix just
before last-copy level `j`):

* **Exposure.** The prefixes `x = (y, g, t_{<j})` reach `eq_{j−1}` with `E^a_j` rows
  `c_x = j_{E_j}·[y_j ≠ t_j]·σ_y S'_g S'_{t<j}`, where `σ_y = s'_0 S'_y`. These are `2^{n−1+s}`
  generic points of `Z_q^{n'}`. Projection (#49 §7(iii)) needs a hidden part of `B_j`, and the
  rows span everything. **PL is vacuous.**
* **Two-sidedness.** `B_j D_{j,¬t_j} ≈ 0`. Lemma 4.1 cannot drop `B_j`, and LWE with secret `B_j`
  is not available, because `B_j` is not one-sided. Making it one-sided means making the
  departure target uniform, which changes the values of witnesses in `dep_j` (above).
* **End step.** Each class string's pad is a sum of `c_x U^{(j)}`-terms (one per mismatch) and
  Tseitin terms. With twisting these pad rows affinely span their space once the class exceeds
  the width. By the leaf dichotomy
  (`MaskedLeaf.mask_of_affine_relation`, `separator_iff_no_affine_relation`) the noiseless
  projected values then **determine the label**. No statistical step can finish.
  * The consistent string's equality pad is `0`, so `α = e_{t}` already annihilates the
    equality blocks. The class label is protected only by the twisted, fat Tseitin and orphan
    pads, never by the cube structure itself.

## 3. Which barriers the "no witness below" condition removes

| Barrier | Applies to ML_i / reroutes | Applies to the ECF | Why |
| --- | --- | --- | --- |
| Witness-pair consistency (PR #61 §4) | yes | **no** | No decryption passes through `Γ_t`. Witnesses beside it (in `dep_j`) pin only the departure target, which no step needs to change |
| SZK barrier (#49 §6) | for path-dependent decryption | **no** | Canonical decryption, and no witness in the class |
| Hybrid-count barrier | to statement-dependent hops | **no** | The hop is local: `¬φ(t)` is checkable |
| Rank jump (#56 §1) / pass-count sensitivity (PR #61 §6, CVW18 Claim 9.8) | yes, a structure change adds one independent noise direction | **no** | The flip changes the eq top rows of a fixed class structure. Zero-noise matrices factor through the same row spaces in both hybrids, and no zero lies in `Γ_t` |
| Single-cut rectangles | removed by `no_honest_rectangle` | removed | as for MP2 |

So, in contrast to `ML_i` and the reroutes, the ECF is **not expected to be false** for any `c`
or `n`. Its single-pass analogue (the class is one path) is #56's provable ERASE flip. It is a
genuine target. What blocks it is the toolbox, not a distinguisher.

## 4. The remaining core: the fat sibling-pad lemma (FSP)

After phase 1 and leaf-first, and with the comparator in the scalar-row model of PR #61 §2, the
ECF reduces to one statement per meeting block. It is the overcomplete cut lemma of #55 §10 with
three differences:

* it is statement-independent;
* it has no zero inside the class;
* it has a witness-carrying sibling.

> **FSP (open).** Let `B ∈ Z_q^{n'×m}` be hidden and uniform, with `D ← A^{-1}` such that
> `B D_{chain} = U` (uniform, used nowhere else) and `B D_{dep} = E` (an encoding of zero, shared
> with witness prefixes). Let `2^{N}` prefixes `x` (`N = (c−1)n − 1 + s`) carry GGH15 values
> `w_x = ℓ + c_x B + (other blocks) + e_x`, where:
> * `c_x = σ_{y(x)}·τ_x` are twisted product rows;
> * `e_x = Σ_i X_{x<i} E_{i,x_i} D_{x>i}` is the upper-level GGH15 noise;
> * everything is given succinctly by the encodings.
>
> Then the label added to every chain continuation, `{w_x D_{chain} D_{…} + L}`, is hidden.
> Equivalently, the noise `e_x D_{chain}` hides the exact affine relations `Σ α_x c_x = 0`
> (`Σα_x = 1`), whose coefficients are of size `q`.

* **Not provable by CVW18 moves** (§2): PL is vacuous, `B` is two-sided, and there is no
  separator.
* **Not the PRF of CVW18 Lemma 7.4.** Lemma 7.4 (BPR/BLMR, `S_x a + E_x`) has this shape, but
  needs **fresh** flooding noise per output and gives security only for oracle queries. Theorem
  7.5 gets the white-box encoding by Cor. 5.9, the whole encoding pseudorandom given `J·A_0`.
  The WE publishes two left vectors whose difference exposes the root (Remark 5.8). A local
  Cor. 5.9 for the class would need a root for `Γ_t` covered by an `I_n`-type block. The class
  is entered through `2^N` fat prefix rows, not through a root.
* **Not attacked.** We found no short relation among the pads (generic twisted products, an
  SIS-type search in dimension `≥ 2^{20}`), and no zero to feed a rank test. On true statements
  the decryptor knows `ρ_*mask` and `ρ_*mask'` from witnesses, but the class values differ from
  either by a full-size pad. A distinguisher needs a short `α` with `Σ α_x c_x = 0` and
  `Σ α_x ≠ 0`.

So the ECF is **open, reduced to FSP, with no known barrier and no known proof technique**. It is
an LWE statement about GGH15 noise on overcomplete structured rows, which is the frontier that
#55 §5 and #49 §7(v) also reached. The difference is that here it is local, zero-free and
falsifiable.

## 5. Regime (d) as a complete walk: reroutes are unavoidable, and dominated by (b)

* **Reroutes are necessary** (`card_le_width_mul_of_fixed_partition`, Lean). Suppose the final
  class map `f : {0,1}^n → Fin W` of the consistent strings is the same in every hybrid. A walk
  from all-`mask` to all-`mask'`, each hop changing at most `k` consistent labels, then has
  `2^n ≤ W·k`. Every class flips at some hop, all of its strings at once. An ECF changes
  `k = 1` consistent label, so an ECF-only walk needs `W ≥ 2^n`. Every polynomial-width walk
  must change the class structure between thresholds, that is, reroute.
* **The regime-(d) reroute is fat and keeps the consistency barrier.** `(t, eq ↦ mask')` and
  `(t+1, eq ↦ mask)` give identical labels. They differ in the chain of the last copy, from the
  first level `j` where `t` and `t+1` differ. As in PR #61 §1–§2 this is a sequence of
  single-*state* merges with a hidden scalar row `δ_i` (the comparator block still exposes 3
  directions). The difference is that `2^{h−n}` chain prefixes `(y, g, t_{≤i})` now leak `δ_i`,
  instead of one.
  * Witnesses `w` with `w_{≤i} = t_{≤i}` (through `eq_i`, departing at `i + 1`) and `w'`
    (departing earlier) both decrypt to `ρ_*mask'`. Every CVW18 move on `δ_i` changes one and
    not the other, exactly as in PR #61 §4.
  * The fat reroute is stated as the open node `AdvancedEncryption.WE.LastPass.fat_reroute`, with
    PR #61's rank hypothesis `rows^{2(2c−1)} ≥ 2^n`.
* **The walk** (`lastpass_walk`, a Lean sketch, complete modulo the two open nodes).
  * Alternate ECF at `t` and fat reroute `t → t+1` for `t = 0, …, 2^n − 1`.
  * A `CloseAt` chain lemma (telescoping and Cauchy–Schwarz, as in `Hybrid.hardAt_chain`)
    composes the `2^{n+1}` hops with loss `2^{n+1}·(h+1)·hopLoss`.
  * It ends in `(2^n, false)`, where `mask` occurs only in the challenge.
* **Cost, if both nodes held.**
  * Widths and moduli are those of MP2 (`pq-we-multipass-ggh15` §4): `d ≈ 1.3·10^4 n' ≈ 2^{23.6}`,
    `m ≈ 2^{40}`, ciphertext `≈ 2^{97}` bits for MP2 and slightly more for MP3.
  * Per-departure classes on the last copy, needed by the §2 proof attempt, multiply the
    last-copy width by `n + 1`: `≈ 2^{30.6}`, `m ≈ 2^{47}`, total `≈ 2^{106}`.
  * The hop count is `≈ 2^{129}·poly`, so premises of `≈ 400` bits are needed, as in MP2.
  * `rows^6 ≥ 2^{128}` holds.
  * All of this is far below brute force (`≈ 2^{188}`, `we-circuitsat-bruteforce-explicit-cost`).
* **Comparison with regime (b)** (comparator on the first copy, PR #60 §4 / PR #61).
  * In (b) the flip part is a *single-prefix* ERASE, provable from LWE: the eq class at the end
    of pass 1 is the single prefix `t`, and every pass-2 departure falsifies an equality clause.
  * The open part of (b) is the reroute (`ML_i`).
  * Regime (d) makes the flip fat (the ECF, open) and keeps a reroute with the same barrier,
    now with `2^{h−n}` leaking prefixes.
  * **Regime (d) is therefore not an improvement.** The escape of the fixed-cut counting
    (PR #60 §3(d)) is paid for twice.
* **Caveat for regime (b)** (found on the way). PR #60 §4 step 1 erases the consistent subtree
  `(t, t, ·)` "by a falsified clause of `Tseitin(φ)`".
  * No single clause is falsified by all gate completions `g`, so this is not one #56 ERASE.
  * The cut lemma (#55 §6) does not apply either: every sub-CNF of `Tseitin|_t` inside a proper
    prefix of the gate levels is satisfiable, so it needs `2^{s−1} ≤` width.
  * A provable route is a chain along the gate evaluation `g(t)`: one single-clause ERASE per
    gate, about `2^{12}` hops, with per-class blocks along the chain.
  * That chain is `t`-dependent class structure. It lies in a witness-free subtree, but creating
    it is itself a split, which no existing node proves.

## 6. Repairs tried

1. **Thin first copies** (bit-independent constraint secrets on the earlier copies; CPRF block
   still twisted; comparator bit-independent there anyway). Here the gate levels must come
   *after* the last copy, as in PR #60's layout (the comparator is the identity on them).
   Twisted gate levels placed before the last copy would make the class fat again, in `g`.
   * *Gain.* At every first-copy level the prefix rows are `(alive-pattern ⊗ σ_i)`, with one
     fixed `σ_i`. They span at most `2n + 2` directions, so root-first PL works through the first
     copy and along the last-copy chain down to the meeting blocks.
   * Each meeting block `B_j` is exposed in **one** direction. Its pad is
     `[y_j ≠ t_j]·p_j` with a single uniform `p_j`. A class value is then
     `v(y, g) = v(t, g) + Σ_{j ∈ Δ(y)} p_j·D(g)`, a fixed function of the consistent values and
     of independent uniform `p_j`. So the orphans reveal nothing about the label beyond the
     consistent string.
   * **The ECF reduces to the flip of the single consistent subtree**, which is the regime-(b)
     step with the gate-chain caveat of §5.
   * *Loss.* Zero-evaluation matrices over a variable partition `X | Y` become
     `Σ_{k<K} f_k(x) g_k(y)·(single-pass product)`, with clause indicators `f_k g_k`. Their rank
     is `≤ K·t` (`thin_cross_rank_le`, Lean), against `t^3` for twisted first copies (PR #61).
     With `K ≈ 1.25·10^4` clauses and `t ≈ 2^{23.6}`, `K·t ≈ 2^{37} < 2^{64}`, so balanced
     partitions of `n = 128` variables are in range of CVW18 Claim 9.8. This holds on statements
     chosen so that the gate values split as well (gates on `X` first, then gates on `Y`), as in
     PR #61 §6.
   * Hence every structure-changing hop (the fat reroute, PR #61's reroute) is heuristically
     refutable in the thin variant.
   * **Verdict: the twisting that makes the class fat is the twisting that protects the
     reroutes. Neither can be bought without the other.**
2. **Permutation-form equality checks** (a width-2 XOR block per position, no zeros in the level
   matrices). Canonical decryption needs the equality block to vanish on consistent strings
   (#55 §5, PR #61 §5(2)). The zero moves into the top rows of the "match" state, so leaf-first
   stops at the top for every match-landing transition. **No gain.**
3. **Untie the eq top** (give `eq_L` a fresh top block, then LWE with it as secret). In the real
   hybrid the eq top equals the gt top. With bit-independent `R_L`, the targets
   `R_L·mask + E` out of `eq_{L−1}` and `gt_{L−1}` share both secret and public matrix, so
   their difference is small and the tie cannot be switched by LWE in the clear.
   * Per-class comparator secrets would remove the tie, but they break canonical decryption:
     witnesses follow different class sequences, so the `R`-products differ.
   * Palindromic first/last-copy secrets with short inverses (`R_y R_z^{-1} = I` iff `y = z`)
     do not help either: gt and eq still share `R'_{L,c}`. **No gain.**

## 7. Exact remaining gap

* **`AdvancedEncryption.WE.LastPass.equality_cube_flip`** (open). Its minimal form is FSP (§4):
  a local, zero-free, falsifiable LWE statement about GGH15 noise on overcomplete twisted rows
  next to a witness-carrying sibling.
  * No known barrier excludes it (§3).
  * The CVW18 moves cannot prove it (§2).
  * It is provable in the thin variant, which however loses the reroutes (§6.1).
* **`AdvancedEncryption.WE.LastPass.fat_reroute`** (open). It carries PR #61's consistency
  barrier, so it is at least as far from the toolbox as `ML_i`.
* **Together** they give the complete WE walk for MP2/MP3 in regime (d) (`lastpass_walk`,
  sketch).
* **On its own** the ECF does not. A proof of FSP would give a proof of the ECF, but the WE still
  needs a reroute. The better host for a reroute proof remains regime (b), where the flip side is
  already provable (modulo the gate chain of §5).

## 8. Formal results of this PR

* `WE_LastPassGGH15` (definition): `copyOff`, `cmpMatFrom`, `lastPassTop`, `lastPassView`.
* `LastPass.equality_cube_flip` (open), `LastPass.fat_reroute` (open).
* `LastPass.lastpass_walk` (sketch from the two open nodes; its `CloseAt` chain lemma is proved
  in the solution).
* Complete proofs:
  * `card_le_width_mul_of_fixed_partition`: label-only walks need `|X| ≤ W·k`;
  * `exists_unique_first_mismatch`: equality cubes;
  * `thin_cross_rank_le`: rank `≤ K·t`;
  * `not_sat_of_copies_differ`: orphans are not zeros;
  * `departure_kills_chain_clause`: the forced departure zero.

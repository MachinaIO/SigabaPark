---
title: WE - Lemma 4.4 with an exposed root row holds on short-lift complements; with shared pad secrets the co-located zero flip is exact, so APG reduces to point insertion
refs: [definition:WE_CircuitSAT, definition:GGH15, definition:WE_MaskedGGH15, note:pq-we-native-hop-designs, note:pq-we-witness-prf-masked-evaluator, note:pq-we-multipass-ggh15, note:pq-we-hybrid-count-barrier, theorem:AdvancedEncryption.WE.NativeHop.zero_entry_hint, theorem:AdvancedEncryption.WE.NativeHop.lex_prefix_cubes, theorem:AdvancedEncryption.WE.MaskedGGH15.masked_decrypt, theorem:AdvancedEncryption.WE.ExposedRoot.basis_change_preimage, theorem:AdvancedEncryption.WE.ExposedRoot.reachable_closure, theorem:AdvancedEncryption.WE.ExposedRoot.colocated_part, theorem:AdvancedEncryption.WE.ExposedRoot.cover_pad_card, theorem:AdvancedEncryption.WE.ExposedRoot.dead_level_invisible, theorem:AdvancedEncryption.WE.ExposedRoot.uncovered_readings_collide, theorem:AdvancedEncryption.WE.ExposedRoot.phase_one_kernel_break]
tags: [witness-encryption, ggh15, candidate, proof, open-problem]
---
Design-AI sub-task (oo) on `Def_WE_CircuitSAT` and its capped version (PR #105, cost `≤ 2^100`).
The candidate is the additive-pad masked γ⊗-GGH15 WE "APG" of `pq-we-native-hop-designs` §6.
Open PR #110 (note "pq-we-zero-entry-crossing") reduces its pad merge PM and point insertion PI to
a zero-flip lemma ZF, and isolates the missing tool as "CVW18 Lemma 4.4 with one exposed root
row" (L4.4-r). This note tests L4.4-r, starting from the smallest case. Open PRs are cited by
number only. CVW18 = Chen–Vaikuntanathan–Wee, ePrint 2018/360, read from the full text (Lemmas
3.2, 3.9, 3.12, 3.13, 4.1, 4.4, 5.10, 5.11, Remark 7.2).

The seven `ExposedRoot.*` theorems have complete Lean proofs (Mathlib only). Everything else is an
informal argument checked step by step by the submitting agent. The statistical and LWE steps
cite CVW18's lemmas; they are not formalized.

## 0. Answer

1. **L4.4-r, smallest case (ℓ = 1): true** (§1, §2). With `R = P A_0` public, the level-1
   preimages can be replaced by Gaussians conditioned only on `R D_{1,b}`. The proof is CVW18's
   Bonsai proof of Lemma 4.4, run on the rows that complete `P` to an invertible `W`, plus noise
   smudging (`+λ` bits of `log q`). It works because `P` has entries in `{0, ±1}`, so `W^{-1}` is
   short.
2. **L4.4-r at deeper levels: only for complements with a short lift** (§2). The same proof
   applies at level `i` to any complement direction `C = P' A_{i-1}` such that
   `W^{-1}[0; I]` is short. When the reachable rows `V_{i-1}` have large entries (products of
   secrets), the complement noise is tied to the exposed noise `V_{i-1} E` and smudging fails. We
   do not claim the full-complement version.
3. **The standalone one-slot flip is false; the sibling flip is exact.**
   * With no cover, two readings below the zero entry collide (`uncovered_readings_collide`), so
     #110's (cover) condition is necessary.
   * With a sibling slot, flipping is an exact law equality after one L4.4-r step (§1).
4. **General ℓ: the co-located cover flip CC** (§3). Suppose all pad slots share their secrets
   (one γ⊗ pad block `M^{pad} ⊗ S^{pad}`, unit start weights; same size as APG). Then for two slots
   with the same prefix `π`, the difference rows `h_i = a_i^{(c_1)}` have a short lift at every
   level. Root-first L4.4-r on that one direction, plus CVW18's leaf-first steps for the cover,
   makes flipping `(L, b)` an exact law equality.
   * No induction on ℓ is needed.
   * PM steps 1 and 2 are instances of CC.
5. **Rest of the walk except PI** (§4, §5).
   * Dead slots are reshaped by CC ("shortening"). Their entries after the dead level are reset by
     CVW18 Lemma 4.4 on the dead rows, which are unreachable (`dead_level_invisible`). This
     replaces the flooded renormalisation of #110.
   * The final full-cube hybrid is CVW18 itself: the full slot masks `R` (`cover_pad_card`).
6. **What remains: PI only** (§7). Every tool above preserves the law of every value `V(z)`. PI
   changes `V(k)` and is valid only because `C_Ψ(k) ≠ 0`. It is the point version of the masked
   two-vector lemma, not a zero-crossing problem.
7. **Cost correction** (§6). The leaf-first steps (CVW18 Lemma 5.10) need pad width
   `n' ≈ λ log q / O(1)`. At `n' ≈ 2^{10}`, `log q ≈ 2^{16.5}` they are broken in polynomial
   time (`phase_one_kernel_break`). With wide pads, APG costs about `2^{108}`–`2^{110}` bits,
   **above `2^{100}`**. The `≈ 2^{97}` of `pq-we-native-hop-designs` §7 and of MP2 assumed
   `n' ≈ 2^{10}`.

## 1. The smallest case: one mask block, ℓ = 1

**Matrices.** Levels `i = 0, …, h`. Every `A_i ∈ Z_q^{N×m}` comes from TrapSam. Its rows are
blocks: the mask rows `A_i^{mask}` (bit-independent secrets `R_i`) and the rows `a_i^{(c)}` of
each pad slot `c` (secrets `m^{(c)}_{i,b} S_{i,b}`, short and invertible). There is no constraint
block. The CPRF block has no zeros, so CVW18's leaf-first steps remove it first. Afterwards
`u_O` is uniform and `u_C = u_O − R`. Preimages:

`D_{i,b} ← A_{i-1}^{-1}(Ŝ_{i,b} A_i + E_{i,b})`, `Ŝ_{i,b} = diag(R_i, m^{(c)}_{i,b} S_{i,b}, …)`,
with `E_{i,b}` Gaussian of width `σ_E`.

**Public view:** the exposed row `R = P A_0` with `P = [I | I | …]` (unit start weights), that
is `R = A_0^{mask} + Σ_c a_0^{(c)}`, and all `D_{i,b}`. The secrets, the noises and every `A_i`
are hidden. The full scheme adds `u_O`, `u_C` and `⌊mask⌉ + μ`, `mask = r_0 R_* A_h^{mask}`.

**L4.4-r (ℓ = 1).** Let `W = [P; P']`, where `P'` consists of the unit rows of the slot blocks.
Then `W^{-1}` has entries in `{0, ±1}`.

* `H_0` is the real view.
* `H_1` differs only in `D_{1,b} ← A_0^{-1}(W^{-1}[P Y_{1,b}; U_b])`, with `U_b` fresh uniform and
  `Y_{1,b} = Ŝ_{1,b} A_1 + E_{1,b}`. By Lemma 4.1 this is a Gaussian conditioned only on
  `R D_{1,b} = P Y_{1,b}`, so the exposed reading keeps its law exactly.

Claim: `H_0 ≈_c H_1` (§2).

**One slot, no cover: false.** Take one slot with program `[b = p_1]` at level 1 and `1` after.
`G'` flips `m_{1,1−p_1}` to `1`, so `Δ = (1−p_1)∗`.

* In `G`, for `b = 1 − p_1`, `R D_{1,b} = R_1 A_1^{mask} + e_1`.
* The mask block is bit-independent, so `R D_{1,b} D_{2,0}` and `R D_{1,b} D_{2,1}` differ by
  `R_1(E_0 − E_1) + e_1(D_{2,0} − D_{2,1})` (`uncovered_readings_collide`). That is short; for
  `h > 2`, multiply by a common suffix.
* In `G'` the two readings differ by a pseudorandom slot term.

The distinguishing advantage is `≈ 1`. In the full scheme, use two strings of `Δ` with the same
unsatisfied-clause pattern.

**Two sibling slots: exact.** Slots `c_0 = 0∗` and `c_1 = 1∗`. Flip `c_0`'s `(1, 1)` from `0` to
`1` (PM step 1 for the empty prefix):

1. Run CVW18 leaf-first (Lemma 5.10 with Lemma 4.1) on `c_1`'s rows, levels `h, …, 2`. All of
   `c_1`'s entries there are `1`.
2. Apply LWE with secret `a_1^{(c_1)}`: the target `S_{1,1} a_1^{(c_1)} + E` becomes a fresh
   uniform `U`.
3. Apply L4.4-r. Level 1 now enters the view only through `P Y_{1,1}`, whose slot part is
   `X + U`. Here `X = E` in `G` and `X = S_{1,1} a_1^{(c_0)} + E` in `G'`.
4. `X + U` is uniform and independent of the rest for every `X` (`cover_pad_card`), so `G` and
   `G'` have the same law.
5. Undo steps 3, 2 and 1.

## 2. L4.4-r with a short-lift complement

**Statement (L4.4-S).** Fix a level `i ≥ 1` and an invertible `W = [V'; P']` acting on the rows
of `A_{i-1}`. Write `B = V' A_{i-1}` and `C = P' A_{i-1}`. Assume:

* (a) in the current hybrid, `A_{i-1}` enters the view only through `B` and through the level-`i`
  preimages. For example, `V'` contains the reachable rows `V_{i-1}`
  (`V_0 = P`, `V_i = rowbasis[V_{i-1} Ŝ_{i,0}; V_{i-1} Ŝ_{i,1}]`), whose closure is given by
  `reachable_closure`;
* (b) **short lift:** `G = W^{-1}[0; I]` has small entries.

Then replacing `D_{i,b} ← A_{i-1}^{-1}(Y_{i,b})` by `A_{i-1}^{-1}(W^{-1}[V' Y_{i,b}; U_{i,b}])`
(`U` fresh uniform) is indistinguishable. The assumption is `LWE_{m_1, 2m, q, U, D_σ, D_σ}`, the
one of CVW18 Lemma 4.4, with `m_1 ≥ 2N log q`. The statistical loss is `2^{-λ}` when
`σ_E ≥ 2^λ ‖G‖ σ_LWE · poly`.

**Proof.**

* *Exact basis change.* The sets `{D : A D = Y}` and `{D : (W A) D = W Y}` are equal
  (`basis_change_preimage`), so the preimage is the same Gaussian under `[B; C]`. Since `A_{i-1}`
  is uniform and `W` invertible, `B` and `C` are independent and uniform.
* *Bonsai* (CVW18 Lemma 3.13, as in the proof of Lemma 4.4). Split the columns `m = m_1 + m_2`.
  * The reduction samples `A^{(2)}` with a trapdoor and `B^{(1)}` uniform.
  * It takes `C^{(1)}` as the LWE secret, with public `X_1 ← D_σ^{m_1×2m}` and challenge
    `Y_1 = −C^{(1)} X_1 + E_chal` or uniform.
  * It samples the level noise `E` itself and outputs
    `D = [X_1; A^{(2)-1}([V' Y − B^{(1)} X_1; P' Ŝ A_i + P' E + Y_1])]`.
* *Noise.* With a real challenge the noise is `E + Δ`, where `Δ = G E_chal`. Then `V'Δ = 0`, so
  the exposed noise `V' E` is unchanged, and `P'Δ = E_chal`. By (b), `Δ` is short, and smudging
  (CVW18 Lemma 3.2) gives distance `2^{-λ}` from the real hybrid. With a uniform challenge the
  complement target is uniform, and Lemma 3.13 re-assembles the new hybrid.
* *No self-defeat* (#84, #110 `trapdoor_not_lossy`). The embedded secret `C^{(1)}` has no
  trapdoor; only `A^{(2)}` has one. Zero children are allowed, because Lemma 4.4 holds for
  arbitrary `Z`. ∎

**Where (b) holds.**

* At the root, with `V' = P`, which has entries in `{0, ±1}`.
* For the difference direction of two co-located slots with shared secrets (§3).
* For the rows of a dead slot (§4), where `W` is a permutation.

**Where (b) fails.** Take the full complement of `V_{i-1}` at deep levels. `V_{i-1}` has entries
of size `(σ√n)^{i-1}`, and `G` then has entries near `q`.

* The complement noise `P' E` is then tied to the exposed noise `V E`. When `ker V` has no short
  vectors, `V E mod q` determines `E`.
* The reduction must compute `V E` itself yet leave `P' E` to the challenge.
* We see no fix, and we do not claim this version.

So "phase 2 on the whole complement" (the literal L4.4-r of #110 §8) remains unproved. The
proofs below use only (b)-type directions.

## 3. The co-located cover flip CC (general ℓ)

**Scheme change (APG').** All `n + 1` pad slots share their secrets. The pad part is one γ⊗ block
`M^{pad}_{i,b} ⊗ S^{pad}_{i,b}` with diagonal `0/1` programs, and every slot has start weight `1`
in `u_O`. This is CVW18's γ⊗ form, as for the constraint block. Each slot keeps its own rows
`a^{(c)}_i`, so pads of different slots stay independent: `pad_c(z) = S^{pad}_z a_h^{(c)}`. Size
and cost are those of APG. Of the attacks checked in `pq-we-native-hop-designs` §6, only
subtraction refers to the slot secrets, and it needs them to be bit-dependent, which they still
are. A separate cryptanalysis of the sharing is still advisable.

**Statement (CC).** Let `d ≠ c` be pad slots and `L` a level such that:

* (i) `d` and `c` have the same entries `[b = π_i]` at every level `i < L` (co-located on the
  prefix `π`);
* (ii) `m^{(c)}_{L,b} = 1` and every entry of `c` at levels `> L` is `1`.

Then flipping `m^{(d)}_{L,b}` (either direction) gives `G ≈_c G'`, uniformly in `Ψ`, the
constraint block and the other slots. The loss is `L` L4.4-S steps, `h − L + 1` LWE steps, and
`L` smudging terms.

**Proof.** At each level `i − 1 < L`, change the basis of the two slot row blocks of `A_{i-1}` to
`g_{i-1} = a^{(d)}_{i-1} + a^{(c)}_{i-1}` and `h_{i-1} = a^{(c)}_{i-1}`. In block form
`W = [[I, I], [0, I]]`, with `W^{-1} = [[I, −I], [0, I]]`, so (b) holds.

* *The `g`-chain is self-contained.* By (i) and the shared secrets, the targets are:
  * `g`-row: `[b = π_i] S_{i,b} g_i + E^{(d)} + E^{(c)}`;
  * `h`-row: `[b = π_i] S_{i,b} h_i + E^{(c)}`.
* *Every reachable row* has `(d, c)`-part `β_π (S_π, S_π)` (`colocated_part`), so it lies in the
  span of the `g`-rows.

Steps:

1. **Root-first L4.4-S on the `h`-direction, levels `1, …, L`.**
   * At the root, `R` contains `g_0`, and `h_0` is hidden.
   * At level `i`, `h_{i-1}` appears only in the level-`i` preimages. Its own level-`(i−1)`
     target was replaced in the previous step, and the `g`-row target involves `g_{i-1}`, which
     is an independent coordinate.
   * After the step, every `h`-row target at levels `≤ L` is a fresh uniform.
   * At level `L`, the `g`-row target at `(L, b)` is `X + T`, where:
     * `X` is `d`'s own contribution: `E^{(d)}` before the flip and `S_{L,b} a_L^{(d)} + E^{(d)}`
       after it;
     * `T = S_{L,b} a_L^{(c)} + E^{(c)}_{L,b}`.
2. **Leaf-first on `c`, levels `h, …, L+1`** (allowed by (ii)). Then `a^{(c)}_L` appears only
   in the level-`L` `g`-row targets (`T`, and the analogous term at the other child if `c` is
   active there). LWE with secret `a^{(c)}_L` and public `S_{L,·}` makes `T` a fresh uniform `U`.
3. `X + U` is uniform and independent of everything else for each `X` (`cover_pad_card`). Nothing
   else depends on `m^{(d)}_{L,b}`: `V_{L-1}` and the levels `< L` do not involve it, and the
   levels `> L` use the original rows. So `G` and `G'` have the same law.
4. Undo steps 2 and 1. ∎

**PM.** Siblings `c_0 = π0∗` and `c_1 = π1∗` at `L = |π| + 1`.

* Step 1: flip `c_0`'s `(L, 1)` from `0` to `1`, with cover `c_1`.
* Step 2: flip `c_1`'s `(L, 1)` from `1` to `0`, with cover `c_0`, which is now `π∗`.

Both are CC instances, for every prefix length.

**Why (cover) is now local.** (i) and (ii) say that `c` pads all of `πb∗ ⊇ Δ` and shares `d`'s
reachable direction. Without shared secrets, `G = W^{-1}[0; I]` contains `S^{(d)-1}_π S^{(c)}_π`
and (b) fails. That is the obstruction #110 met.

## 4. Dead slots without flooding

* **Entries after a dead level are free.** Let `d` have both entries `0` at level `j`.
  * The `d`-rows of `A_{j-1}` have targets `E` at level `j`. So `a_j^{(d)}` is hidden, and its
    columns vanish in every reachable row at levels `≥ j` (`dead_level_invisible`).
  * CVW18 Lemma 4.4 on the `d`-rows (the complement is a set of unit rows; `W` is a permutation,
    so (b) holds) replaces the `d`-row targets level by level, for levels `j+1, …, h`.
  * After that, `d`'s entries after `j` do not enter the view and can be reset. Undo the steps.
* **Shortening.** Let `d` have prefix `p` (`|p| = L`) and be dead at `L + 1`. While `p∗` is a live
  slot, flip `d`'s `(L, p_L)` from `1` to `0` by CC with cover `p∗`. Then `d` has prefix `p_{<L}`
  and is dead at `L`.
* **Preparing PI.** A free slot with prefix `k_{<j}` and dead at `j` gets entries `[b = k_i]`
  after `j` (free). Flipping `(j, k_j)` then yields exactly the point cube `{k}`. This is PI_j.
* **The walk** (lexicographic, `lex_prefix_cubes`).
  * Hop `k → k + 1` with `k = x01^t`: PI_j for `k` from a free slot with prefix `x`, then `t`
    merges.
  * Each merge leaves a dead slot with prefix `p`, shortened while `p∗` is live. Older free slots
    are shortened as the merge chain passes their level.
  * Invariant: every free slot's prefix is a prefix of the next point.
  * Live plus free slots: `n + 1`. #110's flooded renormalisation (its §5) is not needed.

## 5. The last hybrid is CVW18

At the end one slot `c*` is the full cube `∗`.

1. Leaf-first on `c*` frees `a_0^{(c*)}`.
2. `R = P A_0` contains `a_0^{(c*)}` as a one-time pad, so `R` is uniform and independent of the
   other rows of `A_0` (`cover_pad_card` with `M = I`). `A_0` is now hidden as `J A_0` is in
   CVW18.
3. CVW18 Lemma 5.11 (Lemma 4.4 root first, with no exposure left) makes every remaining `D_{i,b}`
   Gaussian.
4. `A_h^{mask}` then appears only in `mask = r_0 R_* A_h^{mask}`, which is uniform.

So the final step of `pq-we-native-hop-designs` §6 ("expected, not proved") is proved.

## 6. Accounting and a parameter correction

* **Hops.**
  * About `2^{128}` PIs and `2^{128}` merges. Each merge costs `2` CC flips plus at most `n + 1`
    shortenings; each PI costs one reset. That is about `2^{128}(n + 5) ≈ 2^{135}` macro-hops.
  * Each macro-hop runs `≤ h ≈ 2^{12}` L4.4-S or leaf-first steps. Counting one hop per
    multi-secret LWE instance gives `≈ 2^{147}` hops; one hop per secret row gives `≈ 2^{170}`.
  * With the rule `premise ≈ 128 + 2 log₂(hops)` (`pq-we-multipass-ggh15` §4,
    `pq-we-hybrid-count-barrier`), this is about **420–470-bit LWE**, plus whatever PI needs.
* **Smudging.** `+λ` bits plus `log ‖G‖` (`≤ 1` bit here) in `log q`, under `1%`.
* **Width.** The leaf-first steps (CC step 2, §5) use CVW18 Lemma 5.10: LWE with secret
  `a_i^{(c)}` (dimension `n'`, the pad width) and the short public `[S_{i,0}; S_{i,1}]`.
  * Exact linear algebra finds a nonzero integer left kernel `z` of that `2n' × n'` matrix, with
    entries at most the Hadamard bound `(√n' ‖S‖)^{n'}`. Then `z (S a + E) = z E`
    (`phase_one_kernel_break`).
  * At `n' ≈ 2^{10}`, `‖S‖ ≈ 2^7` that is `≈ 2^{12400} ≪ q ≈ 2^{90000}`, so this assumption is
    **false in polynomial time**.
  * CVW18 Remark 7.2 requires `n = Ω(λ log q)`. The Lindner–Peikert estimate
    `n ≈ (λ + 110) log₂(q/σ) / 7.2`, at a 420–470-bit premise, gives `n' ≈ 2^{22.5}`–`2^{23}`
    for the pad block (`n + 1` slots) and for the CPRF block.
  * Then `N ≈ 2^{29.5}`–`2^{30}`, `m ≈ N log q ≈ 2^{46}`–`2^{46.5}`, and the ciphertext is
    `≈ 2L m^2 · 16 ≈ 2^{108}`–`2^{110}` bits. This still keeps the constraint block at
    `n' = 2^{10}`. If PI or attack 5 of `pq-we-witness-prf-masked-evaluator` §5 needs that block
    wide too, the cost is `≈ 2^{122}`.
  * **APG and APG' do not meet `2^{100}`**, even with PI proved. The same applies to MP2, whose
    width is computed with `n' ≈ 2^{10}` in `pq-we-multipass-ggh15` §4.
  * Possible repairs, not analysed here: ring or module GGH15 levels (saves the ring degree in
    the ciphertext), or fewer simultaneous pad slots.

## 7. The remaining gap: point insertion PI

**PI_j(k).** Take an APG' hybrid in which:

* every `z < k` is padded by prefix-cube slots;
* a free slot `d` has prefix `k_{<j}`, is dead at `j`, and has entries `[b = k_i]` after `j`;
* `C_Ψ(k) ≠ 0`.

Claim: flipping `d`'s `(j, k_j)` from `0` to `1` is LWE-indistinguishable, uniformly over the
adversary's choice of `Ψ`.

* **Why the tools above cannot prove it.** L4.4-S, leaf-first steps, CC and the dead-slot moves
  all preserve the law of each value `V(z)`. PI changes `V(k)` from `mask − C(k)` to a padded
  value, and for a witness `k` it is false (decrypt at `k`). So any proof must use
  `C_Ψ(k) ≠ 0`, through the constraint block.
* **Why the constraint block cannot be the cover.** A clause falsified by `k` is active on every
  prefix that has not yet satisfied it, not on `k_{<j}` alone. So it is not co-located with `d`.
  Making clause blocks co-located would give a polynomial walk, against
  `pq-we-hybrid-count-barrier`. In APG' the exponentially many hops are exactly the PIs.
* **Status.** PI is the point version of the masked two-vector lemma
  (`pq-we-witness-prf-masked-evaluator` §6): hide `mask − C(k)` at one non-witness string, given
  everything below `k` padded. It is open, and no attack is known.

## 8. Formal results (Lean, complete proofs)

| Theorem | Content | Used in |
| --- | --- | --- |
| `ExposedRoot.basis_change_preimage` | `Winv W = 1` ⇒ (`A D = Y` ⇔ `(W A) D = W Y`) | §2 exact basis change |
| `ExposedRoot.reachable_closure` | `V' S = K V` ⇒ `V'(S A + E) = K (V A) + V' E` | §2 hypothesis (a) |
| `ExposedRoot.colocated_part` | `Σ_q β_q [q = π] X = β_π X`, for two blocks at once | §3 |
| `ExposedRoot.cover_pad_card` | `M` invertible over a finite ring ⇒ `#{u : x + M u = t} = 1` | §1, §3, §5 |
| `ExposedRoot.dead_level_invisible` | reachable `d`-parts vanish after a level with both entries `0` | §4 |
| `ExposedRoot.uncovered_readings_collide` | the two readings below an uncovered zero differ by `R_1(E_0 − E_1) + e_1(D_{2,0} − D_{2,1})` | §1 |
| `ExposedRoot.phase_one_kernel_break` | `z S = 0` ⇒ `z (S a + E) = z E` | §6 |

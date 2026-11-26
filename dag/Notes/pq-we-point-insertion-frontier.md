---
title: WE - point insertion for APG′ splits into one dead-chain lengthening and G+1 clause-frontier flips; every proved move keeps an alive-prefix invariant that PI breaks
refs: [definition:WE_CircuitSAT, definition:WE_MaskedGGH15, definition:GGH15, note:pq-we-native-hop-designs, note:pq-we-zero-entry-crossing, note:pq-we-plr-hop-rank-and-erase, note:pq-we-ggh15-vocabulary-open-lemmas, note:pq-we-witness-prf-masked-evaluator, note:pq-we-hybrid-count-barrier, theorem:AdvancedEncryption.WE.NativeHop.lex_prefix_cubes, theorem:AdvancedEncryption.WE.ZeroCross.departure_first_difference, theorem:AdvancedEncryption.WE.PointInsert.cover_flip_keeps_allowed, theorem:AdvancedEncryption.WE.PointInsert.dead_reset_keeps_allowed, theorem:AdvancedEncryption.WE.PointInsert.copy_keeps_allowed, theorem:AdvancedEncryption.WE.PointInsert.no_first_level_cover, theorem:AdvancedEncryption.WE.PointInsert.pad_reuse_span]
tags: [witness-encryption, ggh15, barrier, open-problem]
---
Design-AI sub-task (rr) on `Def_WE_CircuitSAT` and its capped version (PR #105, cost `≤ 2^100`).
The candidate is APG′: the additive-pad masked γ⊗-GGH15 WE of `pq-we-native-hop-designs` §6, with
all pad slots sharing their secrets (one γ⊗ pad block), as introduced in open PR #111 (note
"pq-we-exposed-root-reachable-lemma"). PR #111 proves the cover flip CC, the pad merges, the
dead-slot moves and the final hybrid, and leaves one step open, the **point insertion PI**. This
note attacks PI. Open PRs are cited by number only; "CC", "L4.4-S" and "dead reset" refer to
#111 §2–§4.

The five `PointInsert.*` theorems have complete Lean proofs (Mathlib only). Everything else is an
informal argument checked step by step by the submitting agent.

## 0. Answer

1. **PI is not proved.** No attack on PI is known either.
2. **Reduction (§2).** In APG′ the "point" `k` is a witness string, so PI pads the whole subtree
   `{k} × {0,1}^G` of gate values. By Tseitin unit propagation this subtree is the disjoint
   union of `G + 1` prefix cubes `Q_t`. Each `Q_t` fully falsifies one clause `κ_t`, whose deepest
   variable is the last level of `Q_t`. PI then splits into:
   * one **dead-chain lengthening** `LEN` (a zero flip that changes no value, `Δ = ∅`);
   * `G + 1` **frontier flips** `NCF(Q_t, κ_t)`, each a cover flip whose cover is the clause slot
     `κ_t`, except that `κ_t` is not co-located with the flipped slot;
   * `G` CC merges and `G` CC shortenings, which are proved in #111.
3. **Why the frontier flip is not CC (§3).** CC needs the cover to have the flipped slot's
   entries above the flip level. A clause with `r ≤ 3` variables is alive on at least
   `2^{L−r}` prefixes of length `L − 1`, while the free slot is alive on one. The clause's
   pseudorandom target is therefore read by more than `n'` prefixes, so it is no one-time pad for
   `k`'s prefix (`pad_reuse_span`). This answers ideas (1) and (2) of the task: the "anti-zero"
   entry exists, but it is shared.
4. **Obstruction theorem (§4, §5).** Every program-changing move proved so far keeps one
   invariant: *every pad slot is alive only on prefixes that already fully falsify a clause.* The
   moves are the cover flip CC (even with clause covers, in a variant where clauses share the pad
   secrets), dead resets, and a new exact move SCC (symmetric co-located copy, §5). Under the
   invariant no pad is ever alive on both values of the first-level variable, so the final
   hybrid is unreachable. The invariant is extended in §5 to cover SCC's clause copies.
   * `LEN` breaks the invariant, although it changes no value. So "law-preserving" is not the
     right dividing line, unlike #111 §7: the missing ingredient is a move that makes a slot
     alive on a non-falsified prefix.
   * `NCF` keeps the invariant but is not a cover flip.
5. **ERASE (idea 3, §6).** APG′'s shared pad block does not supply ERASE's class. ERASE needs a
   copy of the falsified clause's rows read only by `k`'s prefix. APG′'s pad rows carry no clause
   rows, and the global clause rows are read by every prefix alive for the clause.
6. **Cost and premise if `LEN` and `NCF` were available (§7).** About `2^{153.6}` hops, so a
   premise of about 436-bit LWE plus the atoms' own losses. The cost is unchanged from #111: about
   `2^{108}`–`2^{110}` bits, above `2^{100}`.

## 1. The statement

**Setting.** This is APG′ of #111 §3. Masked γ⊗-GGH15 for the Tseitin CNF `Ψ` of `φ`
(`Def_WE_MaskedGGH15`; `pq-we-witness-prf-masked-evaluator` §5):

* Levels read `w` (128 levels), then the gate values in topological order, with the output gate
  last.
* There is one pad block `M^{pad}_{i,b} ⊗ S_{i,b}` with diagonal 0/1 programs, shared
  bit-dependent secrets, unit start weights, and own rows `a^{(c)}_i` per slot `c`.
* Decryption is `V(z) = mask − C_Ψ(z) + Σ_c pad_c(z) + noise`.
* The clause block `M^{con} ⊗ S'` reads clause `κ` through the program `[b falsifies κ's
  literal]` at `κ`'s variable levels and `1` elsewhere, with its own secrets `S'`.

**PI_j(k)** (#111 §7). In the hybrid where:

* every `z` with witness part `< k` is padded by prefix-cube slots;
* a free slot `d` has prefix `k_{<j}`, is dead at `j`, and has entries `[b = k_i]` after `j`;
* `φ(k) = 0`, so every `z = (k, g)` violates some clause;

flipping `d`'s entry `(j, k_j)` from `0` to `1` is LWE-indistinguishable, uniformly over the
adversary's choice of `Ψ`. Its effect is to pad all `2^G` strings `(k, g)`.

## 2. Frontier decomposition of PI

Let `g* = g*(k)` be the correct gate values on input `k` (`g*_out = 0`). By
`departure_first_difference`, every `g ≠ g*` has a first gate `t` with `g_t ≠ g*_t`. So the
subtree `k∗` is the disjoint union of:

* `Q_t = k g*_{<t} (1 − g*_t) ∗`, for each gate `t`;
* the leaf `Q_out = {k g*}`.

Each `Q_t` fully falsifies one clause `κ_t`:

* If the correct value is `g*_t = 1`, some input `a` is `0` and `Q_t` sets `c = 0`. It falsifies
  `(a ∨ c)`.
* If `g*_t = 0`, both inputs are `1` and `Q_t` sets `c = 1`. It falsifies `(¬a ∨ ¬b ∨ ¬c)`.
* The leaf falsifies the unit clause `(out)`.

In each case every variable of `κ_t` lies in the prefix, and the deepest one is the last level
`L_t` of the prefix. So `κ_t`'s slot program is `1` on all of `Q_t` and all-ones after `L_t`.

**Walk inside the subtree** (deepest first, two extra slots):

1. **`LEN`.** Take the free slot `d` (prefix `k_{<j}`, dead at `j`). Reset its entries after `j`
   to `[b = (k g*)_i]` up to the output level and to `0` at the output level (dead reset). Then
   flip `(j, k_j)` from `0` to `1`. Now `d` has prefix `k g*_{<out}` and is dead at `out`. No
   value changes (`Δ = ∅`), but `d` is now alive on the non-falsified prefixes `k g*_{<i}`.
2. **`NCF(Q_out, (out))`.** Flip `d`'s `(out, 0)` to `1`. This pads the leaf.
3. For `t` from the last gate down to the first:
   * **`NCF(Q_t, κ_t)`.** A free slot with prefix `k g*_{<t}`, dead at `t`, flips
     `(t, 1 − g*_t)`.
   * **Merge** (CC, #111 §3) the siblings `Q_t` and `k g*_{≤t}∗` into `k g*_{<t}∗`. The merge
     leaves a dead slot with prefix `k g*_{<t}`.
   * **Shorten** (CC with cover `k g*_{<t}∗`, #111 §4) that dead slot to prefix `k g*_{<t−1}`,
     dead at `t − 1`. This is the free slot of the next `NCF`.
4. The result is the cube `k∗`. The walk then continues as in #111 §4 (merges along the trailing
   ones of `k`).

Per point: one `LEN`, `G + 1` `NCF`s, `G` merges, `G` shortenings and `O(G)` resets.

**Alternative.** If step 1 resets the output entry to `[b = g*_out]` instead of `0`, steps 1 and
2 merge into one flip at level `j` that pads the single full string `k g*`. That is a "string PI".
It is both invariant-breaking and value-changing.

## 3. The frontier flip is CC without co-location

**`NCF(Q, κ)`.** A free slot `d` has prefix `π = p_{<L}` (`Q = p∗`, `|p| = L`) and is dead at
`L`. The clause `κ` has all its variables at levels `≤ L`, deepest at `L`, and `p` falsifies it.
The claim is that flipping `d`'s `(L, p_L)` from `0` to `1` is indistinguishable.

* After the flip, `d` and `κ` have **identical programs at levels `≥ L`**. Both are dead on
  `1 − p_L` at `L` and all-ones after `L`. CC's hypothesis (ii) holds with `κ` as cover.
* Hypothesis (i) fails. CC needs equal entries above `L`. `d` has `[b = p_i]`, but `κ` has `1` at
  every non-clause level. As alive sets, `d` is alive on the single prefix `π` of length `L − 1`,
  while `κ` is alive on all `2^{L−1−r'}` prefixes that agree with `p` on `κ`'s `r' ≤ 2` upper
  variables.
* **Consequence for the proof of CC** (#111 §3, steps 1–3). In the basis
  `g = a^d + w a^κ`, `h = w a^κ` at level `L − 1`, the `h`-direction is reachable from every
  other prefix alive for `κ`, so root-first L4.4-S cannot hide it.
  * Leaf-first on `κ` (levels `h … L+1`, no zeros there) does make `κ`'s level-`L` target a
    uniform `U`.
  * But the target pair becomes `(X + U, U)`, which reveals `X` (`X = E` before the flip,
    `X ≈ U^d` after).
* **Pad reuse** (`pad_reuse_span`). The reading row of prefix `x` on `U` is `c_x = w s S_x`. For
  `L > 128` there are far more than `n'` readers, so generically `c_π = Σ_{x≠π} λ_x c_x` and
  `c_π U = Σ λ_x c_x U`. A one-time-pad argument for `π` alone is therefore impossible.
  * This is a statement about proofs, not an attack: the readings `c_x U` reach the adversary
    only inside `V(z)`, mixed with the mask and other clauses.
* **Special case that is provable.** When `κ`'s variables are all the levels `≤ L` (so `L ≤ 3`),
  `κ` is co-located with `d` and `NCF` *is* CC. This needs clauses to share the pad secrets and
  `w = ±1` (the variant APG″ of §5). It is irrelevant for Tseitin beyond the first three levels.
* **Ideas (1) and (2) of the task.**
  * The violated clause gives exactly the "nonzero entry" `κ(L, p_L) = 1` and the all-ones tail
    that CC needs.
  * The localized root-first/leaf-first step at `κ`'s last level is CC step 2, and the
    exposed-root lemma L4.4-S is CC step 1. Step 1 requires the complement direction to be
    unreachable, and `κ`'s rows are reachable from every prefix that has not yet satisfied `κ`.
  * The lexicographic cube structure (one point merged into `≤ 128` cubes) is already fully used
    by §2 and the merges. It does not create co-location at `κ`'s level.

## 4. The alive-prefix invariant (obstruction theorem)

**Model.** A slot program is `m : ℕ → Bool → Bool` (0-indexed levels). It is *alive on the
length-`ℓ` prefix of `x`* if `m i (x i) = 1` for all `i < ℓ`. A clause `κ` is *fully falsified*
by that prefix if it is alive there and `κ i c = 1` for all `i ≥ ℓ`, i.e. all its variables are
below `ℓ` and falsified. Write `Fals_ℓ` for the fully falsifying prefixes. Fix a predicate `T`
("allowed prefixes") with `Fals ⊆ T`. Define

`J_T`: every pad is alive only on prefixes (of length `≥ 1`) in `T`.

**Moves.**

* (a) **Cover flip.** This is CC, generalized to allow a clause as cover. Flip `d`'s `(L, b)`, in
  either direction, with a cover `c` (another pad or a clause) that has `d`'s entries at all
  levels `< L`, `c(L, b) = 1`, and only `1`s after `L`. #111's merges and shortenings are cover
  flips with pad covers.
* (b) **Dead reset.** `d` has both entries `0` at `L`; change its entries after `L` (#111 §4).
* (c) **Copy.** Replace `d` by a copy of a program alive only on `T` (SCC, §5).
* L4.4-S, leaf-first steps and the final CVW18 step do not change programs.

**Theorem (Lean, one step each).**

* `cover_flip_keeps_allowed`: (a) preserves `J_T`.
* `dead_reset_keeps_allowed`: (b) preserves `J_T`.
* `copy_keeps_allowed`: (c) preserves `J_T`.

The real scheme has all-zero pads, so it satisfies `J_T` for every `T`. By induction on the
number of moves, **every hybrid reachable by these moves satisfies `J_Fals`**: pads are alive
only on prefixes that already fully falsify a clause.

**Consequences.**

* Every pad alive anywhere is alive on a prefix of length 1. Under `J_Fals` this needs a unit
  clause on the first-level variable (`no_first_level_cover`, with `T = Fals`). A Tseitin CNF
  has none, so **cover flips and dead resets never pad any string**. In APG′ proper, clauses
  cannot even be covers, because their secrets `S'` differ from the pad secrets and the short
  lift of #111 §2 (b) fails. The statement then holds with an empty clause set, and no pad is
  ever alive.
* **What breaks `J_Fals`.**
  * PI breaks it: `d` becomes alive on `k_{≤j}`, a witness prefix, which falsifies no Tseitin
    clause.
  * `LEN` breaks it, although no value changes.
  * `NCF` (from a free slot) does not break it: its new alive strings are `Q ⊆ Fals`.
  * So the hops of #111's walk that are not cover flips are exactly the `J`-breaking `LEN`s,
    which are law-preserving, and the `NCF`s, which are value-changing. #111 §7's "every tool
    preserves the law of each `V(z)`" is true but not sharp.
* **The free slots are the problem.** #111's walk recycles free slots, alive on witness
  prefixes, from earlier merges. Every such slot ultimately comes from a PI. A proof of the walk
  needs a move that creates aliveness on a non-falsified prefix. No such move is proved, and
  none follows from LWE through the cover or copy patterns.

## 5. A new exact move: symmetric co-located copy (SCC), and why it does not help

**SCC.** Let `d ≠ c` be slots with shared secrets and start weights `1` and `w ∈ {±1}`.
Suppose that:

* their entries agree at every level except `L`;
* `c(L, b) = 1` and `c(L, 1−b) = d(L, 1−b) = 0`.

Flipping `d(L, b)` from `0` to `1`, so that `d` becomes a copy of `c`, is indistinguishable after
`L` root-first L4.4-S steps. No leaf-first step is needed, and `c` may have zeros below `L`.

**Proof.**

1. Above `L` the slots are co-located. As in CC step 1, root-first L4.4-S on `h = w a^c`
   (short lift `[[I, wI],[0, I]]^{-1}`) makes every `h`-target at levels `≤ L` a fresh uniform.
2. At levels `≥ L`, use `g_i = a^d_i + w a^c_i` and `h_i = w a^c_i`. The programs agree there, so
   these are two closed chains with identical programs and independent uniform rows.
3. At level `L`, branch `b`, the `g`-target is `S h_L + E` before the flip and `S g_L + E` after
   it. On branch `1 − b` it is `E` in both.
4. So before the flip only the `h`-chain is read below `L`, and after it only the `g`-chain.
5. Swapping `g_i ↔ h_i` for `i ≥ L` maps one view onto the other. The preimage law depends on
   `(A_i, Y)` only through the coset `{D : A_i D = Y}`, which is invariant under a simultaneous
   row permutation. The two hybrids have the same law. Undo step 1. ∎

**Uses.**

* With a pad partner, SCC duplicates a pad. It is covered by (c), and `J_T` is kept.
* **Clause copies (variant APG″).** Put the clause block into the pad block (shared secrets,
  `j_κ = ±1`). Take a zero slot, dead at level 0, and dead-reset its entries after level 0 to
  `κ`'s. If `κ` contains the level-0 variable (`κ ∈ Cl₀`), SCC at `L = 0` makes it a pad copy of
  `κ`, which pads the clause cube `Q_κ`. That cube contains no witness for any `Ψ`, so it is
  consistent with every attack.
  * This breaks `J_Fals`, so it is the one invariant-breaking move proved here.
  * APG″ multiplies the clause-block width by the pad width `n' ≈ 2^{22.5}` (#111 §6). The
    ciphertext rises to roughly `2^{130}` bits, so APG″ is of theoretical interest only.

**Extended invariant and level-0 lock.** Let `T_ℓ(x)` hold when some clause is alive on the
prefix and is either fully falsified or in `Cl₀`. Track two properties together:

* (A) `J_T`;
* (B) no pad has both level-0 entries `1`.

Assume that for each bit `b` there is a prefix of length `≥ 1` starting with `b` that is not in
`T` (condition C_b). Then (A) and (B) are preserved by cover flips, dead resets, pad copies and
SCC clause copies:

* **Cover flips at `L ≥ 1`:** `cover_flip_keeps_allowed`; level 0 is unchanged.
* **Cover flips at `L = 0`:** impossible by `no_first_level_cover`, since a cover for bit `b`
  would be alive on the prefix given by C_b.
* **Dead resets:** they never touch level 0.
* **SCC with a clause partner at level `L`:** the partner must agree with `d` at level 0, so by
  (B) it lies in `Cl₀`. Its copy is alive only on `T` (`copy_keeps_allowed`) and has a `0` at
  level 0.

Hence no pad ever has both level-0 entries `1`. In particular there is no full-cube slot (the
final hybrid) and no half-cube `{x_0 = b}`.

**C_b holds for Tseitin** when the output gate does not read the first-level variable. Take
`x = (w, g*(w))` with `w_0 = b`, cut just before the output level. The prefix is consistent, so
no clause is fully falsified, and every `Cl₀` clause is fully assigned and satisfied.

## 6. Idea (3): ERASE and the shared pad block

ERASE (`pq-we-plr-hop-rank-and-erase` §3) erases a subtree with a falsified clause in the
positional candidate. Its step 4 uses a one-time pad `c^κ · U^{eq,κ}` on a **(class, clause)**
block, i.e. a copy of clause `κ`'s rows that only the eq class reads.

In APG′:

* The only rows read by `k`'s prefix alone are the free slot `d`'s rows, and they carry the pad
  function, not clause rows.
* The global clause rows are read by every prefix alive for `κ` (§3, pad reuse).

Giving each pad slot its own copy of the clause block (a `slot ⊗ clause` tensor) does not help
either. `V(k)` still contains the *global* clause reading, and switching that off on `d`'s
region is the comparator/class partition of the positional design, whose class split
(`pq-we-plr-hop-rank-and-erase` §4) is the reroute problem APG was built to avoid. So #108's "PI
is ERASE without a separate class" stands: the shared pad block does not supply the class.

The mask block cannot serve as a cover either. It is alive everywhere, but its top rows are the
challenge `mask`, so leaf-first on it is the WE statement itself. The CPRF block cancels in
`u_O − u_C`, so it is not in the exposed reading that a cover must absorb.

## 7. What a proof of PI must contain; accounting

**Open atoms** (APG′, uniformly over `Ψ`):

* **`LEN`:** turn a free slot with prefix `k_{<j}`, dead at `j`, into one with prefix
  `k g*_{<out}`, dead at `out`.
  * No value changes. It breaks `J_Fals`.
  * It is a zero crossing at level `j` with live departures (`pq-we-zero-entry-crossing` §2).
* **`NCF(Q, κ)`** (§3): a cover flip with a non-co-located clause cover.
* **Or instead, one "string PI" per `k`** (the alternative in §2).

By §4–§5, no combination of CC, dead resets, SCC, L4.4-S and leaf-first steps proves them. Any
proof needs a new step type that either:

* creates aliveness on a non-falsified prefix, which `LEN` needs; or
* uses a pseudorandom target shared by exponentially many prefixes as a pad for one of them,
  which `NCF` needs.

**Accounting if both atoms were hops.**

* Per point: `G + 1 ≈ 2^{12}` `NCF`s and `2G` CC flips, each with at most `h ≈ 2^{12.05}`
  internal steps, so about `2^{25.6}`. Over `2^{128}` points this is about `2^{153.6}` hops, plus
  #111's w-level merges (`≈ 2^{147}`).
* With premise `≈ 128 + 2 log₂(hops)`, that is about 436-bit LWE, plus the atoms' own losses.
* Width: `n + 3` pad slots. Cost: as in #111 §6, about `2^{108}`–`2^{110}` bits.

## 8. Formal results (Lean, complete proofs)

| Theorem | Content | Used in |
| --- | --- | --- |
| `PointInsert.cover_flip_keeps_allowed` | a cover flip (pad or clause cover; co-located, `1` at `(L,b)`, all-ones tail) keeps "pads alive only on `T`" when `Fals ⊆ T` | §4, §5 |
| `PointInsert.dead_reset_keeps_allowed` | resetting entries after a dead level keeps the invariant | §4, §5 |
| `PointInsert.copy_keeps_allowed` | replacing a pad by a program alive only on `T` keeps the invariant | §4, §5 |
| `PointInsert.no_first_level_cover` | under the invariant, a non-allowed prefix through bit `b` rules out every level-0 cover for `b` | §4, §5 |
| `PointInsert.pad_reuse_span` | `c_π = Σ λ_x c_x ⇒ c_π U = Σ λ_x (c_x U)` | §3, §6 |

---
title: Can a construction change keep every class split of the threshold walk shallow? No at polynomial width (fixed-cut lemma), and the rank jump only moves; costs of the exponential-width arrangements
refs: [definition:WE_CircuitSAT, note:pq-we-witness-prf-masked-evaluator, note:pq-we-masked-evaluator-mechanisms, note:pq-we-split-lemma-attempts, note:pq-we-masked-overcomplete-leaf, note:pq-we-hybrid-count-barrier, note:we-circuitsat-bruteforce-explicit-cost, theorem:AdvancedEncryption.WE.ShallowSplit.fixed_rows_linearIndependent, theorem:AdvancedEncryption.WE.ShallowSplit.fixed_rows_card_le, theorem:AdvancedEncryption.WE.ShallowSplit.large_class_rigid, theorem:AdvancedEncryption.WE.ShallowSplit.class_flip_bound, theorem:AdvancedEncryption.WE.ShallowSplit.small_classes_card]
tags: [witness-encryption, ggh15, candidate, barrier, open-problem]
---
Design-AI sub-task (r) on `Def_WE_CircuitSAT` (128-bit witnesses, NAND circuits of `2^12` gates,
`λ = κ = 128`). The target is the remaining gap of the positional masked γ⊗-GGH15 candidate
(`pq-we-masked-evaluator-mechanisms`). Open PR #56 (note "pq-we-plr-hop-rank-and-erase", not merged
when this note is written, so cited by number) reduces the threshold walk to two kinds of hop:

* **ERASE**: the leaf flip of a non-witness path. It is provable from LWE at any polynomial width.
* **Rerouting**: moving the threshold from `t` to `t+1`. This is a statement-independent class
  split. It is provable by projection (`pq-we-split-lemma-attempts`) only when the split depth `r`
  satisfies `r ≤ log2(class width)`, and a rank obstruction makes deep splits visible on true
  statements.

The question was whether a **construction change** (walk order, re-basing, comparator encoding)
can keep every split shallow at polynomial width. If not, the question is why not, and what it
costs at exponential width.

**Answer.**

1. **No arrangement exists at polynomial width.** This is proved rigorously for every arrangement
   whose hops are prefix-local flips (ERASE or PLR) and reroutes of depth `≤ s`. Such a walk never
   changes the encoding above witness level `n_w − s`, and the *fixed-cut lemma* (Lean, complete
   proof) then forces the row space at that cut to contain `2^{n_w − s}` linearly independent rows.
   Projection needs class width `≥ 2^s`. So the width `D` satisfies `D ≥ 2^{n_w/2} = 2^64`, for
   *every* walk order, re-basing schedule and comparator encoding. No rank heuristic is used (§2).
2. **Allowing deep splits does not help either (the rank jump only moves).** Assume #56's rank
   measurement and a comparator whose rows are determined by its state, as #56's correctness fix
   forces. Then three Lean lemmas show that any walk of statement-independent hops makes every
   automaton state at a rank-testable cut `i` hold at most `max(N, f)` prefixes. Here `N ≈` noise
   dimension `+` width and `f` is the flip size. So the walk needs `2^i / max(N, f)` states, which
   is exponential at `i = 64` (§3).
3. **Exponential width.**
   * Shallow-only arrangements need `D ≥ 2^64`. Every level, gate levels included, costs about
     `m^2` entries with `m ≥ D⌈log q⌉`. The resulting lower bound is about `2^174` bits, under the
     brute-force baseline of about `2^188`.
   * The only explicit fully-provable arrangement found has `D ≈ 2^128`, so it costs `≥ 2^256`.
     That is the PR #49 regime, dominated by brute force.
   * The square-root arrangement of §4 would reach about `2^174–2^184`. It needs one unproven
     lemma, the **sink lemma**: merge a finished depth-`s` subtree into a narrow shared class. That
     lemma is the exact remaining gap (§5).

Arguments outside the five Lean theorems are informal.

## 1. Model

* **Levels.** Witness bits come first (levels `1..n_w`, `n_w = 128`), then the `2^12` Tseitin gate
  levels. The total is `h ≈ 4224`.
* **Hybrids and the walk.** The walk is a sequence of hybrids `H_0` (real) `, H_1, …`, ending at
  a hybrid in which `mask` no longer appears. In `H_t` every path `z` carries a comparator label
  `ℓ_t(z) ∈ {mask, mask'}`. Labels go from all `mask` to all `mask'`.
* **Rows at a cut.** At cut `i`, prefix `x ∈ {0,1}^i` has the joint row `X_x`: the product of the
  level secrets along `x`, all blocks. The comparator value of path `x·u` is a fixed linear
  function of `X_x` once the suffix part of the encoding is fixed (read-once GGH15). Write
  `ρ_t(x) = L_t(X_x)` for the *residual* of `x` in `H_t`: the vector of its comparator values over
  all suffixes `u`.
* **Hops.**
  * *Flips* change labels. A flip is **prefix-local at cut `i`** when, for each suffix `u`, it
    changes the label of `x·u` for at most one prefix `x`. PLR single-path flips qualify, and so
    does ERASE, which rewrites the subtree below `t_{≤ℓ_k}` with `ℓ_k > i`.
  * *Reroutes* change the encoding but not the labels. A reroute has **depth `≤ s`** when it
    changes only the levels below witness level `n_w − s`. The splits of #56 have this form, with
    `s` the split depth.
* **Provability criterion (#56).** A reroute of depth `s` is provable by projection iff the joint
  rows of the involved classes stay linearly independent at every level. This needs class width
  `W ≥ 2^s` at every level of the split subtree, gate levels included.

## 2. The fixed-cut lemma: shallow splits need width `2^{n_w/2}`

**Lean (complete proofs).**

* `AdvancedEncryption.WE.ShallowSplit.fixed_rows_linearIndependent`: take rows
  `X : V → (ι → K)` over a field, and residual maps `L t` that are linear. Suppose every `x` has a
  step `t` and a suffix `u` at which `L_t(X_x)` changes while `L_t(X_y)` at `u` stays unchanged
  for every other `y`. Then the rows are linearly independent.
  *Proof.* Apply `L_t` and `L_{t+1}` to a vanishing combination, subtract, and evaluate at `u`.
* `AdvancedEncryption.WE.ShallowSplit.fixed_rows_card_le`: the same hypotheses give
  `|V| ≤ dim`.

**Application.**

1. Let every reroute have depth `≤ s`, and let `i = n_w − s`. Then no hop changes the levels
   `1..i`, so the rows `X_x` for `x ∈ {0,1}^i` are the same in every hybrid.
2. Every prefix `x` at cut `i` lies above a non-witness path. For a false statement, *all* paths
   are non-witnesses, and with the inputs read first no clause lies inside the first `i < 128`
   levels.
3. That path is flipped by a prefix-local hop, so the hypothesis holds for every `x`.
4. Hence `2^{n_w − s} ≤ D_i`, the joint row dimension at cut `i`.
5. Provability needs `W ≥ 2^s` with `W ≤ D`. So `D ≥ max(2^{n_w−s}, 2^s) ≥ 2^{n_w/2} = 2^64`.

The lemma assumes nothing about the comparator, the order of the walk, or how classes are merged
and re-split below the cut. So it kills ideas (1)–(3) at once:

* **(1) Tree-structured walks, per-level width allocation, level-wise re-randomized classes.** All
  of these are reroutes. The ones of depth `≤ s` leave the cut fixed, and the cut needs
  `2^{n_w−s}` independent rows. Allocating width "growing toward the root" is backwards: the
  forced width sits at the cut, where the tree is already `2^{n_w − s}` wide.
* **(2) Periodic re-basing (statistical merges).** A merge is a reroute. If it is shallow, it
  leaves the cut fixed. If it is deep, it is not provable by projection (and §3 shows it is
  visible).
* **(3) Other comparator encodings** (unary or one-hot positions, several comparators per level,
  segment-wise thresholds over blocks of witness bits). The lemma uses only that the comparator
  value is linear in the joint row and that flips are prefix-local. Segment-wise thresholds change
  the *order* in which paths are flipped, not the fact that each path is flipped once through its
  own prefix.

**What escapes the lemma.** Each escape leaves the problem's constraints or the barriers:

* **Non-prefix-local flips.** One hop would flip a family of paths through many prefixes, for
  example a clause cube on suffix or gate variables. If such cube flips were sound for every
  certified cube, the Tseitin clauses would give a *polynomial-hop* proof, which
  `pq-we-hybrid-count-barrier` excludes. A sound mix is not ruled out by this note.
* **Non-read-once encodings.** Here the comparator value is no longer linear in a cut row. No LWE
  proof technique for such GGH15 encodings is known.
* **Statement-dependent hops.** These are forbidden.

## 3. Deep splits are visible: the rank jump cannot be removed, only moved

#56 §1 measures the rank of `[X_x | e_x]` over rectangles of witness paths: `m + rank{X_x}` once
`|S|, |U| > m + rank`. This rests on CVW18's Claim 9.4 heuristic, which has not been checked
experimentally.

**State-determined rows.** By #56 §2, canonical decryption forces bit-independent comparator
secrets. The comparator part of `X_x` is then determined by the automaton state `κ(x)`, so the
rank test sees which large sets of prefixes are monochromatic. Twisted "junk" directions that every
suffix kills add the same block width to every state, which only raises the threshold `N`.

**Lean (complete proofs).**

* `large_class_rigid`: two colorings with the same monochromatic sets of size `≥ N` have the same
  classes of size `≥ N`.
* `class_flip_bound`: let labels go from all false to all true, with at most `f` prefixes changing
  at any (step, suffix). If the prefixes of `c` share their labels in every hybrid, then
  `|c| ≤ f`.
* `small_classes_card`: if every class has at most `b` members, then `|V| ≤ b · #classes`.

**Argument.**

1. A statement-independent hop must hold on true statements whose only non-witnesses are the
   flipped paths. On those statements the rank test applies at every cut `i` with `2^i` and
   `2^{n_w − i}` larger than `N ≈ m + D` (an *admissible* cut).
2. Flips do not change the rows, and reroutes must keep the rank function. So by
   `large_class_rigid` every class of size `≥ N` is the same in all hybrids.
3. A class is one automaton state, so its members share labels. By `class_flip_bound` its size is
   at most `f`.
4. By `small_classes_card`, the number of states at cut `i` is at least `2^i / max(N, f)`. At
   polynomial `D`, `m`, `f` the cut `i = 64` is admissible and this number is about `2^64`.

So the change of walk order or encoding does not remove the rank jump on true statements. It
moves the jump to whatever cut the arrangement leaves "coarse". This is idea (4). It also
explains why the provable regime of §2 and the visible regime meet at the same width `2^{n_w/2}`.

**Consistency with the hybrid-count barrier.** The walk still has about `2^128` hops, each local.
The obstruction here is per hop: it is the locality of the flips plus the cut factorization of
read-once GGH15. It is not about the hop count.

## 4. Exponential width: lower bound, explicit arrangements, costs

**Cost model.** The ciphertext and the work are dominated by the preimage matrices `D_{i,b}`, of
size `m_{i−1} × m_i`, with entries of about `b ≈ 16` bits. Here `m_i ≥ d_i ⌈log q⌉`, where `d_i`
is the joint row dimension. GGH15 noise grows over `h` levels, so
`log q ≳ h · log2 √m ≈ 4224 · 42 ≈ 2^{17.4}`.

**Lower bound for shallow-only arrangements.**

* `d_{n_w−s} ≥ 2^{n_w−s}` (§2).
* `d_i ≥ 2^s` on the levels of the split subtree, including the `2^12` gate levels, by the
  provability criterion.
* So the cost is at least `b (log q)^2 (2^{2(n_w−s)} + 2^12 · 2^{2s})`.
* The minimum is at `s ≈ 61`: about `2^4 · 2^{34.8} · 2^{135} ≈ 2^{174}` bits. That is **below**
  the brute-force baseline of about `2^188` (`we-circuitsat-bruteforce-explicit-cost`), so cost
  alone does not exclude an exponential-width scheme. It would beat brute force only by a factor
  of `≤ 2^14`.

**Explicit fully-provable arrangement: `D ≈ 2^128`.**

* The "hi" part is one-hot down to cut `n_w − s`, so the `2^{n_w−s}` rows there are independent.
* Each hi value `a` keeps its own lo block of width `2^s`, in which its lo walk has splits of depth
  `≤ s`.
* Every step is ERASE or projection. But the per-`a` blocks coexist, so `D ≈ 2^{n_w} · poly`.
  Recursing inside the lo blocks does not help: without merging finished subtrees, the recursion
  `f(n) = 2^{n−s} f(s)` gives `2^n`.
* Cost `≥ 2^{256}`, as in PR #49 and `pq-we-masked-overcomplete-leaf` §4. **Dominated by brute
  force.**

**Square-root arrangement (not fully proved).**

* The hi part is as above: `2^{n_w − s}` independent rows at the cut, fixed forever.
* **One shared wide lo block** of width `≈ 2^s` serves the current hi value `t_hi`.
* Every other hi value sits in a narrow constant-label **sink** (lt or gt).
* Moving `t_hi → t_hi + 1` moves two depth-`s` subtrees: `t_hi`'s finished subtree from the wide
  block into the lt sink, and `t_hi + 1`'s subtree from the gt sink into the wide block.
* Everything else is ERASE (leaf flips) or projection (splits of depth `≤ s` inside the wide
  block).
* Width: `D ≈ 2^{n_w − s} · d_c` at the hi cut, `≈ 2^s` below it, and small sinks.
* Balancing `2^{2(n_w−s)} d_c^2` against `2^12 · 2^{2s}` gives `s ≈ 61 + (log2 d_c)/2` and a
  cost of about `2^{174} · d_c`. For a comparator chain dimension `d_c` between 1 and `n' ≈ 2^10`
  this is `2^174–2^184`: at most about `2^14` below brute force.
* If constraint blocks must be per class (#56's ERASE variant) for every one of the `2^{n_w−s}`
  hi-level classes, then `D ≈ 2^{n_w−s} K n' ≈ 2^{89}` and the cost is above `2^200`. Then even
  this arrangement is dominated.

## 5. Exact remaining gap

* **Polynomial width: no gap left to fill inside this candidate family.** §2 rules out every
  arrangement whose splits are all shallow (a rigorous counting statement). §3 rules out
  statement-independent deep splits (under #56's rank heuristic). A complete LWE proof for
  positional masked GGH15 at polynomial width needs one of the following, and none is known:
  * non-prefix-local flips, sound in a super-polynomial but sub-cube-count mix;
  * a non-read-once encoding with an LWE proof;
  * statement-dependent hops, which are forbidden.
* **Exponential width: the sink lemma (open).** Fix the positional masked γ⊗-GGH15 encoding with
  bit-independent comparator secrets and ERASE-style per-class blocks. Let `v` be a node at
  witness level `n_w − s` whose whole subtree carries one label (all `mask'`, or all `mask`), and
  whose subtree is encoded in a wide block, with all its joint rows independent. Then the hybrid
  in which `v`'s subtree is re-encoded inside a shared narrow sink block of the same label, already
  holding the subtrees of other nodes, is indistinguishable under LWE. The required advantage is
  `≤ 2^{-256}`, since the walk has about `2^128` hops. The lemma must also hold on true
  statements.
  * It is **not refuted** by §3: at `D ≥ 2^64` no cut is admissible, and the rank test would need
    matrices of side `≥ 2^70`.
  * It is **not provable by projection**: the sink is overcomplete, which is the regime of
    `pq-we-masked-overcomplete-leaf` §3.
  * With it, the square-root arrangement gives a complete LWE proof at about `2^174–2^184`, under
    brute force. Without it, the best complete proof costs `≥ 2^256`.
  * A faithful Lean statement needs the GGH15 vocabulary of open PR #57. It is not stated as a
    node here.

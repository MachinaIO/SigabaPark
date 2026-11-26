---
title: Non-read-once (multi-pass) GGH15 walks - which hypotheses of the fixed-cut lemma fail, a two-pass masked variant, and why re-reading helps against rank tests but not the proof
refs: [definition:WE_CircuitSAT, note:pq-we-masked-evaluator-mechanisms, note:pq-we-plr-hop-rank-and-erase, note:pq-we-split-lemma-attempts, note:pq-we-hybrid-count-barrier, note:pq-we-witness-prf-masked-evaluator, note:we-circuitsat-bruteforce-explicit-cost, theorem:AdvancedEncryption.WE.MultiPass.change_rank_le, theorem:AdvancedEncryption.WE.MultiPass.triangular_card_le, theorem:AdvancedEncryption.WE.MultiPass.no_honest_rectangle, theorem:AdvancedEncryption.WE.MultiPass.anchored_slice_card_le]
tags: [witness-encryption, ggh15, candidate, barrier, open-problem]
---
Design-AI sub-task (t) on `Def_WE_CircuitSAT` (128-bit witnesses, NAND circuits with `2^12`
gates, `λ = κ = 128`). Open PR #59 (note "pq-we-shallow-split-arrangements", not merged when this
note is written, so cited by number) proves a *fixed-cut lemma*. Inside read-once GGH15 walks with
prefix-local flips, it forces width `D ≥ 2^{n/2}` (`n = 128`) on any proof whose reroutes are
provable by projection. PR #59 lists "a non-read-once encoding with an LWE proof" as one of the
escapes left. This note asks whether reading the witness several times can circumvent the lemma
while keeping an LWE proof of the witness-indexed walk.

The four Lean theorems cited have complete proofs. Everything else is an informal argument.

**Answer in one paragraph.** Re-reading does not change the GGH15 algebra. A `k`-pass layout is a
read-once GGH15 encoding over its `L` levels, and the evaluator may run it on all `2^L` level
strings, *mixed* ones included. Of the fixed-cut lemma's hypotheses only one can fail: prefix
locality. It fails only through mixed strings whose values move together with the flips of
consistent strings. In every regime where the counting survives (inert mixed strings, labels read
through one copy per variable, anchored mixed strings), the bound is again exponential, and for
projection proofs it is often *worse* (`D ≥ 2^n`). In the one regime that escapes the counting,
every hop flips mixed strings through many prefixes at once, and neither ERASE nor projection
covers such hops. Re-reading does help on the *attack* side. Single-cut rank tests have no
rectangles to act on (Lean). The variable-partition rank tests of CVW18 §9.3.2 cost `t^{Θ(c)}`
for `c` passes, so with `c ≥ 3` they exceed `2^{64}` dimensions at `n = 128`. The two-pass (or
three-pass) masked variant of §4 is therefore an *unrefuted* polynomial-width candidate, of about
`2^{97}` bits. Its missing lemma is a functionality-preserving deep reroute ("two-pass reroute
lemma", §6), and no known LWE technique proves it.

## 1. Model

* **Layout.** A layout is a sequence of `L` levels, each reading one input variable through
  `var : [L] → [N]`. `k` passes means `var` lists the witness bits `k` times (say in the same
  order). The `2^12` Tseitin gate levels come after the passes.
* **GGH15 ignores `var`.** The encoding consists of `D_{i,b}` for every level `i` and bit `b`.
  The evaluator can multiply any level string `z ∈ {0,1}^L`. CVW18's semantic-security corollary
  (Cor. 5.9, γ⊗-GGH15) never uses the map from levels to input bits.
  * The cut factorization `value(x·u) = X_x · Y_u` at a level cut, and the linearity of residuals
    in the cut row, hold over all of `{0,1}^L`.
  * The masked γ⊗ construction of `pq-we-masked-evaluator-mechanisms` and the ERASE lemma of
    `pq-we-plr-hop-rank-and-erase` transfer level by level.
* **Honest and mixed strings.**
  * A string is *consistent* when every pass reads the same `w`. The honest decryptor uses only
    the consistent strings `w^k`.
  * Every other string is *mixed*. The final hybrid must remove `mask` from mixed strings too, or
    erase them.
* **Labels.** As in PR #59, hybrid `H_t` gives every string a comparator label (`mask` or
  `mask'`). Comparator rows are state-determined, since #56 §2 forces bit-independent comparator
  secrets for canonical decryption. So two strings that reach the same automaton state at a cut
  share their comparator residual on every suffix.

## 2. The hypotheses of the fixed-cut lemma, one by one

PR #59 §2 combines five ingredients.

| | Hypothesis | Read-once | `k` passes |
| --- | --- | --- | --- |
| F1 | Comparator value linear in the cut row (`ρ_t(x) = L_t(X_x)`) | yes | **holds** over all `2^L` strings, mixed ones included |
| F2 | Rows at the cut stay fixed over the interval considered | from depth-`≤ s` reroutes | **holds** in the same way; the fixed cut `L − s` now lies in the *last* pass |
| F3 | Prefix-local flips: some column where only `x`'s residual changes | from read-once | **can fail**, only through mixed strings |
| F4 | Coverage: every prefix at the cut lies above a flipped path | `2^i` prefixes | **holds**; in pass `≥ 2` the consistent prefixes are in bijection with all `2^n` witnesses |
| F5 | Projection needs independent live rows in the split subtree | `2^s` | **holds**; the split subtree now contains the later passes, so it holds *more* live strings |

**Lean (complete proofs).** Both theorems generalize the fixed-cut lemma, and neither assumes
read-once.

* `AdvancedEncryption.WE.MultiPass.change_rank_le` (rank form): at a fixed cut, the matrix of
  residual changes `Δ[x, (t,u)] = L_{t+1}(X_x)_u − L_t(X_x)_u` has rank `≤ D` for any column set.
  The fixed-cut lemma is the special case where `Δ` contains a diagonal.
* `AdvancedEncryption.WE.MultiPass.triangular_card_le`: weaken F3 to a *triangular* hypothesis.
  The flip column of prefix `a` may also change prefixes flipped later, but no earlier one. The
  conclusion is still `#prefixes ≤ D`. This covers walks in which a flip drags along mixed strings
  of prefixes that are flipped later.

Why F3 can fail at a first-pass cut `i`:

* The suffix of a consistent string contains a full later copy of `w`, so it determines `w`.
* Hence in the column `(t, u)` of `w`'s flip, every other prefix `y` gives a mixed string `y·u`.
* F3 asks those mixed strings not to move. A design may let them move.

## 3. Regimes: where the counting survives and where it escapes

**(a) Inert mixed strings** (the hops never change a mixed string's value).

* Then F3 holds automatically at every cut. Each column contains exactly one consistent entry
  (`no_honest_rectangle` with an injective suffix map), and the other entries are inert.
* At a cut in pass `≥ 2` the consistent prefixes are the `2^n` witnesses. So
  `D ≥ #witnesses flipped while that cut is fixed`.
* Shallow reroutes keep a last-pass cut fixed for the whole walk, which gives `D ≥ 2^n`.
* Reroutes that reach first-pass level `i` have `2^{n−i}` live consistent continuations. This is
  the single-pass balance again: `D ≥ 2^{n/2}`. **No gain.**

**(b) Labels read through one copy per variable** (for example, a comparator on pass 1 only, or on
`(w_hi from pass 1, w_lo from pass 2)`).

* Fix the coordinates the comparator does not read (a slice). Inside the slice, F3 holds again
  and the PR #59 lemma applies verbatim.
* Mixed strings are live here (the constraint and CPRF blocks give them path-random rows), and
  they lie inside every split subtree. A reroute at first-pass level `i` of a two-pass layout must
  then keep `2^{n−i} · 2^n` rows independent at the end of pass 2.
* Together with `2^i ≤ D` this gives `D ≥ 2^n`. This is **strictly worse** than read-once unless
  the mixed strings are erased first, and then we are back in regime (a).

**(c) Multi-copy labels, anchored.** All reroutes stay inside passes `≥ 2`, so the first pass is
frozen with at most `W` end states. Mixed strings `(y, z²)` whose `z²` lies outside `y`'s
first-pass class (*orphans*) are inert.

* The strings `(y, w)` with `y` in `w`'s class are co-labelled with `(w, w)` forever. So inside
  the slice `z¹ = y`, F3 holds for the second-pass prefixes of `y`'s class.
* `AdvancedEncryption.WE.MultiPass.anchored_slice_card_le` gives `2^n ≤ W · 2^{n−c} · D` at a
  second-pass cut `c`.
* Projection at second-pass depth `n − c` needs `2^{n−c} ≤ D`. Hence `D^2 · W ≥ 2^n`, that is
  `D ≥ 2^{(n − log W)/2}`. This is the read-once bound again.

**(d) Multi-copy labels, unanchored.** Orphan mixed strings move with the flips of unrelated
consistent strings. Only here does the counting disappear. By `change_rank_le`, a change matrix
with prescribed non-zero consistent entries can have rank 1, for example when every hop changes all
strings whose last copy equals the flipped `w`. The price is concrete:

* **Non-prefix-local flips.** One hop flips the consistent `w^k` together with `2^n − 1` orphans
  `(y, w)`. They are certified by equality clauses, one cube for each first mismatch position, but
  through `2^{n−j}` different nodes for cube `j`. ERASE (#56 §3) handles *one clause on one
  subtree*. A sound "equality-cube flip" is not excluded by `pq-we-hybrid-count-barrier`, because
  the cubes do not depend on `φ` and the walk still has about `2^n` hops. No LWE proof is known
  either.
* **Fat split classes.** Every class at a second-pass level contains a whole first-pass class,
  and some first-pass class has `≥ 2^n / W` strings. All of them are live, so projection needs
  `D ≥ 2^n / W`.

So regime (d) trades the counting obstruction for two unproven hop types.

**Conclusion on (1).** Exactly one hypothesis (F3, prefix-locality) fails for multi-pass
encodings, and it fails only through mixed strings. Whenever it is restored (regimes a, b, c), the
width bound is `2^{Ω(n)}`. Where it really fails (d), the needed hops leave the ERASE/projection
toolbox. **For proofs built from ERASE and projection, re-reading gains nothing and often loses a
factor `2^{n/2}` in width.**

## 4. The two-pass masked variant MP2 (and MP3)

**Construction** (the γ⊗ blocks of `pq-we-masked-evaluator-mechanisms`, with #56's fixes).

* **Levels:** pass 1 reads `w_1..w_n`, pass 2 reads `w_1..w_n`, then the `2^12` Tseitin gate
  levels, so `L = 2n + 2^12 = 4352`. MP3 adds a third pass, `L = 4480`.
* **Secrets:** `Ŝ_{i,b} = diag(P_{i,b} ⊗ R_i, M_{i,b} ⊗ S'_{i,b}, S_{i,b})`.
  * **Comparator `P`:** the reflected-Gray comparator against the threshold `t` on pass 1, and the
    identity on later levels (regime b). The secrets `R_i` are bit-independent (#56 §2). Final
    rows are `mask'` on lt and `mask` on eq/gt.
  * **Constraint block `M`:** the CNF diagonal BP of `Tseitin(φ)`, whose input literals are read
    from the last pass. Add the `2n` **equality clauses** `(z¹_j ∨ ¬z²_j)`, `(¬z¹_j ∨ z²_j)` (and
    the same between passes 2 and 3 for MP3). The constraint secrets `S'_{i,b}` are
    bit-dependent. ERASE needs per-class blocks in pass 2 along an equality chain against `t`
    (#56 §3's class split, here at pass-2 levels).
  * **CPRF block `S`:** as before, reading every level.
* **Left vectors:** `u_O` and `u_C` as in the mechanisms note, with a rank-one difference.

**Correctness (canonical decryption).**

* The honest decryptor evaluates `(w, w, g(w))`.
* Every equality clause holds, so the constraint block vanishes exactly when `φ(w) = 1`.
* At `t = 0` the comparator ends in eq/gt, and `R_i` is bit-independent, so `O − ck = mask` for
  every witness. The canonical value is the same as in single pass.

**Mixed-input attacks.**

* *Classical mixed-input attack* (satisfy different clauses on different copies): blocked. Every
  mixed string falsifies an equality clause, so its constraint product `C(z) ≠ 0` and it
  evaluates to `mask − C(z)`, like a non-witness. No mixed string is a zero, so bundling scalars
  are not needed. The equality clauses do their job inside the constraint block.
* *Single-cut rank tests* (CVW18 Claim 9.4, #56 §1, PR #59 §3): `no_honest_rectangle`. At every
  level cut of a layout that re-reads all variables, the prefix or the suffix determines `w`.
  Honest zeros therefore form a partial permutation, with no `2 × 2` rectangle. The obstruction
  "deep splits are visible", which killed the single-pass PLR hop, **disappears in this form**.
* *Variable-partition rank tests* (CVW18 §9.3.2, Appendix A): these split the *variables*
  `X | Y`, not the levels, and use tensor identities, so they still apply.
  * Their matrix dimension is `ρ = t^{Θ(c)}` for `c` passes. CVW18 states "the running time grows
    exponentially in c" and uses `ρ = t^3` for `c = 2`.
  * The test needs `2^{|X|}, 2^{|Y|} > ρ` with `|X| + |Y| = 128`, so it needs `ρ < 2^{64}`.
  * With `t ≈ 2·(w + n) ≳ 2^{24}`, MP2 already has `ρ ≈ 2^{72}`, outside that range. MP3 is
    further away still (`≈ t^5`).
  * So at `n = 128` no known rank test distinguishes MP2's hybrids. Asymptotically, the test
    returns for `c = O(1)` and `n → ∞`, as CVW18's §11 candidate (`λ + 1` repetitions)
    acknowledges.
* *CGH17 attack* (Chen–Gentry–Halevi, ePrint 2016/998): it needs an input-partitioned program. A
  program that reads every bit on both sides of every cut is not input-partitioned, so the attack
  does not apply.

**Hybrid walk** (the threshold walk of #56).

1. **ERASE.** For threshold `t` (a non-witness), split the eq class below node `t` (end of pass 1)
   along the pass-2 equality chain. Erase each departure subtree `(t, t_{<j}, ¬t_j)` by its
   equality clause `E_j` (`n` hops). Erase the consistent `(t, t)` subtree by a falsified clause of
   `Tseitin(φ)`.
   * Each step is #56's ERASE: leaf-first LWE on `(class, clause)` blocks (CVW18 Lemma 3.9 / Cor.
     5.9, which are layout-independent), then projection on the pass-2 chain, whose classes are
     single nodes, then a one-time pad.
   * **Provable from LWE at polynomial width**, with `n + O(1)` hops per threshold.
2. **Reroute `t → t+1`.** After step 1, `H_t^{done}` and the honest encoding with threshold `t+1`
   give **the same label on all `2^L` strings** (lt ⇔ `z¹ ≤ t`). They differ only in their class
   structure: the old eq chain survives as a separate lt class, and the new chain is not yet
   split. This is a deep, functionality-preserving re-encoding.
   * The LWE instance needed: none known.
   * Projection would need `≥ 2^{n−i} · 2^n` independent live rows (regime b), so it is not
     applicable.

**Width and cost.**

* Width `d ≈ 3 d_R + (3·2^12 + 4n) n' + n ≈ 1.3·10^4 n'`. With `n' ≈ 2^{10}` this is
  `≈ 2^{23.6}`.
* `log q ≈ L · log2 √m ≈ 4352 · 20.6 ≈ 2^{16.5}`, so `m ≈ d log q ≈ 2^{40}`.
* Ciphertext and work are `≈ 2L · m^2 · 16` bits `≈ 2^{97}`. That is about 1.2 times the
  single-pass candidate, far below the brute-force `≈ 2^{188}` of PR #34
  (`we-circuitsat-bruteforce-explicit-cost`).
* The walk has about `2^{128} · (n + 2) ≈ 2^{136}` hops, so premises of about
  `128 + 2·136 = 400` bits are needed (`pq-we-hybrid-count-barrier`). Larger `n'` covers this.
* **With projection-only proofs** (regime b), MP2 needs `D ≥ 2^n`, a cost `≥ 2^{256}`, dominated
  by brute force. Erasing the mixed strings first gives regime (a), that is the single-pass costs
  of PR #59 (`≳ 2^{174}`, with the sink lemma still open).

## 5. Literature (checked from the source texts)

* **CVW18** (ePrint 2018/360).
  * The γ⊗-GGH15 semantic-security result (Thm 5.7, Cor 5.9) is a statement about the whole
    encoding of arbitrary matrices. It never uses the level-to-input map, so input repetition
    does not matter to it.
  * Its applications are a private constrained PRF (Thm 7.5, Type I programs, input-repeating
    allowed) and lockable obfuscation (§8, Type II, random lock). Only the WE candidate (§10)
    uses read-once programs, and it has no proof.
  * §9: the attack is polynomial for input-partitioned programs and "grows exponentially in c"
    for c-input-repeating ones. Claim 9.8 builds functionally equivalent 2-repeating programs
    that are distinguished. The §11 iO candidate uses `λ + 1` repetitions and bundling, with no
    reduction.
  * §1: "For all the applications that can be based on LWE, the adversary cannot trivially obtain
    encodings of zero".
* **GKW17 / WZ17** (lockable / compute-and-compare obfuscation, ePrint 2017/274, 2017/276). Both
  use input-repeating Barrington programs (`inp(i) = i mod n`). The proof makes the whole
  encoding simulatable, because a random lock means no input accepts. There is no honest zero.
* **BGMZ18** ("Return of GGH15", ePrint 2018/511). Dual-input programs, secure in a GGH15
  zeroizing *model* under the bounded-speedup hypothesis. The only LWE part is semantic security
  of the encodings.
* **No paper we found gives an LWE proof for an input-repeating GGH15 encoding in which honest
  inputs evaluate to zero.** Every LWE theorem is of the form "the whole encoding is
  pseudorandom". That form fits ERASE (applied to a subtree with no zeros), but it cannot express
  a reroute, whose two sides share zeros on true statements. CC17 and HHSS17 were not checked.

## 6. Exact remaining gap

**Two-pass reroute lemma (open; the missing lemma of MP2/MP3).**

* **Setting.** Fix `φ` (true or false), the layout and blocks of §4, and a threshold `t` whose
  eq class has been erased (`H_t^{done}`).
* **Claim.** `H_t^{done}` is indistinguishable, under LWE, from the honest encoding with
  threshold `t+1` (fresh `A_i` and secrets at the levels whose comparator or chain changes),
  with advantage `≤ 2^{-264}`.
* **Content.** The two hybrids induce identical labels on all `2^L` level strings. The lemma is
  a GGH15 indistinguishability of two equivalent comparator encodings, inside a scheme whose
  honest zeros exist.
* **Status.**
  * *Not refuted* at `n = 128` for `c ≥ 2`: no single-cut rectangle, and the variable-partition
    tests have dimension `> 2^{64}`.
  * *Not provable by projection* (F5 gives `D ≥ 2^n`).
  * *Not of the "whole encoding pseudorandom" form* that existing LWE proofs of input-repeating
    GGH15 take, because `H_t^{done}` has honest zeros on true statements.
  * With it, MP2 is a complete WE at about `2^{97}` bits.
  * Proving it needs a new technique: an LWE argument for GGH15 *with zeros*, local to a class
    split. That technique is escape (ii) of PR #59, now with the attack side removed at
    concrete `n`.
* **Caution.** Because of CVW18 Claim 9.8, a statement of this lemma for all `n` with `c = O(1)`
  would be false: the two-repeating attack distinguishes equivalent programs. A sound statement
  must take `c ≥ c(n)` passes, with `t^{Θ(c)} > 2^{n/2}`. That is about 3 passes at `n = 128`, and
  `Θ(n / log t)` asymptotically. For the concrete problem (`n = 128`) MP3 is the right instance.

**Escape (d) (unanchored multi-copy labels).** It needs a statement-independent *equality-cube
flip lemma*: flipping, in one hop, `w^k` together with all orphans `(y, w)`, certified by the
equality clauses. This is not excluded by the hybrid-count barrier. It is open and weaker than
the reroute lemma only in that it is a flip, not a re-encoding.

Everything else about multi-pass walks is settled by the four Lean theorems and §3: **with ERASE
and projection as the only proof tools, every `k`-pass layout needs width `2^{Ω(n)}`**, exactly
as PR #59 found for read-once layouts.

---
title: Positional GGH15 WE revisited - row-partitioned trapdoors make reject-class hops and isolated leaf flips provable from LWE; accept-class splits are unavoidable and are the missing lemma
refs: [definition:WE_CircuitSAT, note:pq-we-ggh15-chain-verdict, note:pq-we-function-hiding-crux, note:pq-we-evaluation-oracle-crux, note:pq-we-leaf-view-no-trapdoor, theorem:AdvancedEncryption.WE.Wee.leaf_trapdoor, theorem:AdvancedEncryption.WE.Gray.adjacent_one_bit, theorem:AdvancedEncryption.WE.Positional.free_hops_keep_shared_accept]
tags: [witness-encryption, candidate, repair, barrier, open-problem]
---
Design-AI sub-task: revisit dead WE candidates and try hard to repair them. This note takes the
positional GGH15 candidate G of `pq-we-ggh15-chain-verdict` with its `K_φ` leaf repair, which
survives the recorded attacks but has no proof. The other dead candidates (kernel collision,
rank-one decomposed LWE, rank gap as an LWE-dimension gap; companion note
`pq-we-repairs-collision-rank-gap`, submitted in parallel) all end up at this shape once their
repairs remove the common secret. The verdict note gave two proof obstructions:

1. **leaf-first:** an LWE hop at level `j` needs every level-`(j+1)` target pseudorandom, hence
   the whole suffix, including the accepting leaf rows shared by exponentially many paths;
2. **trapdoor vs LWE:** a reduction holding a trapdoor for `A_j` cannot use LWE on `A_j`.

This note shows that both are narrower than stated. With trapdoors partitioned by **rows**
(states) instead of columns, the leaf-first induction only has to run through the
**reject-closed** states. That makes two hop types provable from LWE. A proved counting theorem
then shows that these two types can never finish the walk, and that the remaining hop type, an
**accept-class split**, is necessary. The split is the precise missing lemma. Arguments are
informal except the theorem `AdvancedEncryption.WE.Positional.free_hops_keep_shared_accept`
(complete proof in this PR).

## Setting

`n = 128` witness bits. Levels `i = 1..n` read `w_i`. A level-`i` state is a comparator state
`σ` (lt, eq, gt in reflected Gray order against the threshold `g`), tensored with the unipotent
tracker `(1, w_1, …, w_n)` for the decided states lt and gt. Eq states carry no tracker, since
their prefix is the known `g_{<i}`, and the transition eq → gt at level `i` enters the tracker
state `(1, g_{<i}, b, 0, …)`, a small fixed vector.

Encodings `D_{i,b} ← A_{i−1}^{-1}(Y_{i,b})` with `A_{i−1} D_{i,b} = Y_{i,b}`. Row block `σ` of
`Y_{i,b}` is `S_{i,b,σ} · A_i^{(π_{i,b}(σ))} + E`, with a **fresh secret per (level, bit, source
state)** (the state-dependent variant of the verdict note). `A_i^{(τ)}` is row block `τ` of `A_i`,
and the tracker part acts inside it. Leaf `A_n`: rows of rejecting final states are uniform, and
rows of accepting final states are the BGG+ leaf `[A − w ⊗ G | B']` (through the tracker; for the
isolated eq-final row, directly with `w = g`). The ciphertext also has
`K_φ ← [A_φ − G | B']^{-1}(u)` and the message under `u`. Decryption on a path `w` with
`φ(w) = 1` is unchanged: `s_wᵀ[A − w⊗G | B']` → `s_wᵀ[A_φ − G | B']` → `s_wᵀ u`.

Call a state **reject-closed** (class `R`) if every continuation from it rejects (lt, and eq
states whose subtree is all-reject). `R` is closed under transitions. All other states form the
**accept class**.

## Repair: row-partitioned (tagged) trapdoors

Sample `A_i = [Ā_i | Ā_i R_i + (H_i ⊗ G)]` (Micciancio–Peikert form with tag `H_i`, diagonal over
states). The real scheme uses `H_i = I`: a full gadget trapdoor. The proof's hybrids use
`H_i = 0` on the `R` rows and `I` elsewhere. By the leftover hash lemma `A_i` has the same law in
both up to `negl` (and `A_i` is never published).

* **(F1) LWE on `R` rows.** For `σ ∈ R`, row block `σ` is `[Ā_σ | Ā_σ R_i]`, which has no gadget
  part. From an LWE sample `S Ā_σ + E_1` the reduction forms `S[Ā_σ | Ā_σ R_i] + E` by multiplying
  by `R_i` and flooding `E_1 R_i`. Obstruction 2 does not apply: it concerns a trapdoor for the
  rows that carry the secret. Here the secret multiplies only the trapdoor-free `R` rows. A
  **column** split `[A_L | A_R]` with a trapdoor for `A_R` is a trapdoor for the whole matrix; a
  **row** split is not.
* **(F2) Partial-target preimages.** The reduction must still output `D ← A_i^{-1}(Y)`. If the `R`
  rows `Y_R` of the target are (computationally) uniform, sample `X` from the Gaussian preimage of
  `Y_A` under the accept-class rows only (they have the gadget trapdoor from the tag), and set
  `Y_R := A_i^{(R)} X`. When the width exceeds the smoothing parameter of `Λ^⊥(A_i)`, the pair
  `(Y_R, X)` is statistically close to (uniform, Gaussian preimage of `(Y_A; Y_R)` under the full
  `A_i`). This is the standard conditioning argument: a Gaussian on a coset of the larger
  lattice `Λ^⊥(A^{(A)})`, conditioned on a coset of the sublattice `Λ^⊥(A_i)`, is the Gaussian on
  that coset, and the conditioning coset is near-uniform above smoothing.
* **(F3) Leaf-first only through `R`.** The rows of `Y_{i+1}` that need pre-sampling are those of
  source states in `R`. Their targets lie in `R` rows of `A_{i+1}` (closure), and the `R` leaf rows
  are uniform. So the induction "replace the `R`-row targets of level `n`, then `n−1`, …, by
  uniform" runs with `O(n)` LWE hops, using F1 at each level and F2 for the preimages above it.
  It never touches accept-class rows. **Obstruction 1 is therefore not about matrices shared
  between states. It is about the accept class.**

## Hop types that are now provable

* **(a) Reject-class reroute.** Change one transition `(i, b, σ)` from a target in `R` to another
  target in `R` (any source `σ`). After (F3), both versions of row `σ` of `Y_{i,b}` are LWE
  samples with the fresh secret `S_{i,b,σ}` on trapdoor-free `R` rows, so both are pseudorandom.
  Cost: `O(n)` LWE hops plus statistical steps.
* **(b) Isolated leaf flip.** Flip the eq-final leaf row, reached only by the path `g`, from
  accepting `[A − g⊗G | B']` to uniform, when `φ(g) = 0`. Plant `A = B R + g ⊗ G`. Then
  `[A_φ − G | B']` has the `−G` trapdoor from `AdvancedEncryption.WE.Wee.leaf_trapdoor`, so `K_φ`
  is simulated without a trapdoor for `B` or `B'` (as in `pq-we-leaf-view-no-trapdoor`). The
  isolated row's target `S[B R | B'] + E` with the fresh last-level secret is then LWE on
  `[B | B']`, with `S B R` from `S B + E` by flooding. The other accepting rows are produced
  honestly, since the reduction knows their secrets.

The verdict note's hop `H_g → H_{g'}` (consecutive Gray thresholds, differing at level `j`) splits
into: flip `g` (type b), then reroute the subtree `g_{≤j}`, now all-reject, into lt (type a),
then **isolate `g'`**. In `H_g` the subtree `(g_{<j}, 1 − g_j)` is decided-accept (eq → gt at
level `j`). In `H_{g'}` it must hold an eq path toward `g'` whose eq-final row is the only one
reached by `g'`, ready for the next flip.

## Why (a) and (b) can never finish the walk (proved)

`AdvancedEncryption.WE.Positional.free_hops_keep_shared_accept`: abstract each hybrid as a routing
`route : paths → final states` and an acceptance `acc` on final states. A type-(a) hop keeps every
accepted path in place and sends rejected paths only to rejecting states. A type-(b) hop changes
acceptance only at final states reached by at most one path. If initially more paths are
accepted than there are final states, then some path is accepted after **any** number of such
hops. The proof keeps the invariant: a final state accepting two paths keeps its fiber and its
acceptance. With polynomial width and the real ciphertext accepting all `2^128` paths, the walk
to the all-reject hybrid must contain hops of another type, and every such hop changes the
routing of accepted paths among accept-class states.

## The missing lemma: accept-class split

The cheapest such hop is a **split**. At level `i`, an accept-class state `σ` with incoming
transitions `T_1 ⊔ T_2` gets a fresh copy `σ'` (new row block of `A_i`, fresh secrets
`S_{i+1,b,σ'}`, the same outgoing transitions as `σ`), and `T_2` is redirected to `σ'`.
Isolating `g'` is a sequence of `n − j` splits along `g'`.

**Exact reformulation.** Let `σ' := R σ` be a *correlated* copy: rows `A_i^{(σ')} = R A_i^{(σ)}`
and targets `Y_{σ'} = R Y_σ` for a short invertible `R`. Then the preimage constraint on `σ'` is
implied by that on `σ`, and the `T_2` targets become `P R A_i^{(σ)} + E` where `P` is the fresh
`T_2` secret. Since `P R` is uniform when `P` is, the correlated split is **identical** to the
merged hybrid. So the split lemma is exactly "a correlated copy is indistinguishable from an
independent copy". The step that needs proof is:

> **Split lemma (open).** In the setting above, with `φ` false, the hybrid in which the `T_2`
> targets are `P A_i^{(σ)} + E` (the merged hybrid) and the one in which they are
> `P A_i^{(σ')} + E` with `σ'` independent are computationally indistinguishable, with loss
> `poly(n) · ε_LWE`.

In the reduction this is LWE with a fresh secret `P` on the accept-class rows `A_i^{(σ)}` while
preimages under `A_i` of targets that are **not** pseudorandom are published. Those targets
contain, after projection by the tracker, the BGG+ leaf rows and `K_φ`. That is the shape of
evasive LWE (excluded as an assumption here). As a *lemma from LWE* it is open, and it is the only
piece missing from a `2^128`-hop proof of this candidate: types (a) and (b) are provable as above,
and the hop accounting of `pq-we-hybrid-count-barrier` fits premises of about 384 bits.

Three facts about the split lemma, to save the next attempt some time:

* **It is not local.** It is false for statements with many witnesses below `σ`. Decrypting two
  witnesses `x_1 y`, `x_2 y` (prefixes from `T_1` and `T_2`, common suffix) gives
  `s_{x_1 y} = u_{x_1} T_y` and `s_{x_2 y} = u_{x_2} T_y`. In the merged hybrid the recovered secrets
  of many such witnesses satisfy the linear relations of the shared suffix factor `T_y`; in the
  split hybrid they do not. So a proof must use that the whole subtree below `σ` has no witness,
  a coNP fact about `2^{n−i}` paths, not the single local fact `φ(w) = 0`.
* **The natural recursion fails.** One would prove a depth-`d` split by walking the subtree below
  `σ` with depth-`(d−1)` hops. But the states below `σ` are shared by `T_1` and `T_2` paths, so
  deeper splits separate `T_1 ∪ T_2` jointly, never `T_2` from `T_1`. Rejecting `T_2` first (target
  → a fresh `R` state) changes the acceptance of `2^{n−i}` paths at once. That needs pseudorandom
  accept-class targets, i.e. the lemma itself. The counting theorem rules out doing it with (a)
  and (b) only.
* **Proved special case (independent secrets).** If the paths below the split had *independent*
  secrets (no products), the needed fact "`{s_w[A − w⊗G | B'] + e}_{w ∈ W}` together with `K_φ` is
  pseudorandom when `φ(w) = 0` on `W`" follows by a hybrid over `w ∈ W`. At step `w`, plant
  `A = B R + w ⊗ G`, simulate `K_φ` with the `−G` trapdoor, and switch `s_w`'s samples by LWE
  (the reduction knows the other secrets). Re-planting between steps is statistical, since `A` and
  `K_φ` have the same law under every planting. So the difficulty lies entirely in the product
  (shared-suffix) structure of the GGH15 path secrets, which is also what makes the ciphertext
  short.

## Attacks checked on the repaired candidate

* **Zero tests:** none on non-witness paths, thanks to the `K_φ` leaf (verdict note, point 4).
  Partial tags exist only in the proof; the real `A_i` has `H_i = I`.
* **Low-rank-plus-noise test on a shared state.** The prefix outputs `a_0 ∏ D` for prefixes `x`
  entering one state `σ` are `u_x A_i^{(σ)} + noise_x`, a matrix `U A + N` whose rows lie near a
  `d_σ`-dimensional space (`d_σ` = LWE dimension × tracker size). A short `α` with `α U = 0`
  would give an exact relation (`α(UA + N)` small), and hence a merged/split distinguisher.
  Finding `α` from `UA + N` alone is an LWE-type problem of dimension `d_σ` with modulus `q`, and
  it is infeasible under the usual GGH15 condition `d_σ ≫ log(q/β)·λ`. So this is a parameter
  constraint, not an attack. It is the reason the split lemma cannot hold for small `d_σ`.
* **Rank attacks (Chen–Vaikuntanathan–Wee type)** need a matrix of zero-test values. There are none.
* **Gray-code visibility** (separate matrices per state): avoided, because all states share one
  matrix `A_i` per level and the tags are internal to the proof.

## Status

* Candidate: positional GGH15 + state-dependent secrets + `K_φ` leaf. The real ciphertext is
  unchanged from `pq-we-ggh15-chain-verdict` (an evasive-LWE-type WE shape plus an accept-all
  comparator). No attack is known.
* Proof: hop types (a) and (b) are provable from LWE with row-partitioned trapdoors (informal;
  F2 is the standard Gaussian conditioning lemma and has not been formalized here). The counting
  theorem shows that splits are necessary. **The split lemma is the single missing lemma.**
  It is an evasive-type statement about one level. A plain-LWE proof of it would give
  post-quantum WE for `Def_WE_CircuitSAT` with about `2^128 · poly(n)` hops.
* Not done: a Lean statement of the split lemma. It needs a vocabulary for state-structured GGH15
  laws (stacked Gaussian preimages via `SigabaNeo.Lattices.Trapdoor.preimage`, tracker
  projection, `K_φ`) that is not yet in the DAG. Its natural first instance is `n − i = 1` (split
  directly above the leaf) with two prefixes per side.

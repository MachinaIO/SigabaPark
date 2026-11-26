---
title: Crossing a zero program entry of a γ⊗-GGH15 slot - standalone zero-flip lemma, why CVW18 crosses zeros only in hidden matrices, and lossy, hinted, flooding and redesign routes
refs: [definition:WE_CircuitSAT, definition:GGH15, definition:WE_MaskedGGH15, note:pq-we-witness-prf-masked-evaluator, note:pq-we-multipass-ggh15, note:pq-we-two-pass-reroute, note:pq-we-two-sided-lwe, note:pq-we-hinted-lattice-assumptions, note:pq-we-tlwe-masked-ggh15-leaf, note:pq-we-ecf-overcomplete-succinct-levels, theorem:AdvancedEncryption.WE.Hints.zero_row_hint_exposes, theorem:AdvancedEncryption.WE.TwoSided.decoded_defect_attack, theorem:AdvancedEncryption.WE.TwoSided.two_child_preimage_consistency, theorem:AdvancedEncryption.WE.TwoSided.decryption_recovers_noise, theorem:AdvancedEncryption.WE.FlipShift.one_zero_child_explains, theorem:AdvancedEncryption.WE.ZeroCross.zero_child_target_determined, theorem:AdvancedEncryption.WE.ZeroCross.trapdoor_not_lossy, theorem:AdvancedEncryption.WE.ZeroCross.lossy_kernel_approx_trapdoor, theorem:AdvancedEncryption.WE.ZeroCross.copy_state_zero_child, theorem:AdvancedEncryption.WE.ZeroCross.shift_overlap_card, theorem:AdvancedEncryption.WE.ZeroCross.first_zero_step, theorem:AdvancedEncryption.WE.ZeroCross.departure_first_difference]
tags: [witness-encryption, ggh15, barrier, open-problem, assumption]
---
Design-AI sub-task (mm) on `Def_WE_CircuitSAT` and its capped version (PR #105, cost `≤ 2^100`).
Every efficient candidate (about `2^97` bits: MP2/MP3 of `pq-we-multipass-ggh15`, and the
additive-pad GGH15 "APG" of open PR #108, note "pq-we-native-hop-designs") misses one tool: an LWE
hop across a **zero program entry** of a γ⊗-GGH15 encoding while the strings that leave there
stay live. PR #108 reduces APG to two lemmas, the pad merge PM and the point insertion PI. Open
PRs are cited by number only.

The seven `ZeroCross.*` theorems have complete Lean proofs (Mathlib only). Everything else is an
informal argument checked step by step by the submitting agent.

## 0. Answer

1. **Standalone statement (§1).** PM and PI are both instances of one **zero-flip lemma**
   `ZF_Ψ`: flip one zero entry of a cube-program pad slot to `1`, in the APG hybrid for an
   adversarial CNF `Ψ`. PM is two such flips (one forward, one backward) whose newly padded set
   is already padded by the sibling slot. PI is one flip at the sink level whose newly padded set
   is the point `{k}`.
2. **The exact obstruction (§2).** CVW18 does cross zero entries, but **only in its second
   phase**: Lemma 4.4 makes `A^{-1}(Z + E)` Gaussian for an *arbitrary* `Z` (zeros included),
   provided `A` is hidden and used nowhere else, which holds root-first because `J·A_0` is
   uniform. Its first phase (Lemmas 4.1 and 5.10, leaf-first) needs uniform targets on all
   children, so it stops at every zero. In APG the slot rows along the prefix `p` have a zero
   child (so phase 1 stops), and they are reachable from the exposed rank-one combination
   `(J'_O − J'_C)·Ā_0` along `p` (so phase 2 cannot start). Running phase 2 from the root pads
   every string, which is the whole WE statement. **The zero-entry gap is the two-left-vector
   gap localised to one slot. It is not a local lattice problem.**
3. **The four angles.**
   * (1) Lossiness: does not help (§3). A matrix under which the reduction samples preimages
     has a trapdoor and is never lossy (`trapdoor_not_lossy`). A lossy matrix with a known
     kernel of its secret part has a short approximate kernel (`lossy_kernel_approx_trapdoor`),
     so it self-defeats like a zero child (`Hints.zero_row_hint_exposes`). A matrix the
     reduction never inverts is already handled by Lemma 4.4, so lossiness adds nothing.
   * (2) Hint-LWE, k-LWE, LWE with side information, entropic LWE: the leak is not a hint *on*
     an LWE sample. Given the public zero child, it *is* the sample:
     `S A + E' = (S E + E' D) D^{-1}` (`zero_child_target_determined`). Every local statement
     about `(Y, D)` is either the trivial identity or false (§4).
   * (3) Flooding on the leaving strings: flooding hides only short shifts
     (`shift_overlap_card`). A crossing turns a short target into a uniform one, so flooding
     would need width `> q` and destroy decryption. Flooding does pay for the noise-only
     renormalisation hops of PM, at `+λ` bits of `log q` (§5).
   * (4) Minimal redesigns: zero entries cannot be removed. Every vanishing pad has a first
     zero step in some row basis (`first_zero_step`). A copy state without program zeros has a
     zero child in the difference basis (`copy_state_zero_child`). The departures of a cube's
     zeros cover its whole complement (`departure_first_difference`). Fresh levels, dead
     states and permutation counters only move the zero to the sink, where it becomes a row
     with two zero children (§6).
4. **No variant closes the gap.** The cost is unchanged: APG and MP2 remain conditional
   `≈ 2^97`-bit candidates, under `2^100` but unproven. The decoded-defect attack does not apply
   to PM (one zero child, one prefix reaching the cut). Its one-zero-child analogue does refute
   every *local* embedding (§7). The remaining gap is a single statement (§8): **Lemma 4.4 with
   one exposed root row**.

## 1. The standalone zero-flip lemma

**Setting (APG, PR #108 §6).** Take the masked γ⊗-GGH15 WE of
`pq-we-witness-prf-masked-evaluator` §5 (`Def_WE_MaskedGGH15`) for a CNF `Ψ` (Tseitin of `φ`).
Add `n` pad slots `c`. Slot `c` is a width-1 γ⊗ block with fresh short secrets `S^{(c)}_{i,b}`,
scalar program entries `m^{(c)}_{i,b} ∈ {0,1}`, rows `a^{(c)}_i` of `A_i`, and it is read only
through `u_O`. Its preimage relations are

`a^{(c)}_{i−1} D_{i,b} = m^{(c)}_{i,b} S^{(c)}_{i,b} a^{(c)}_i + E^{(c)}_{i,b}`.

Decryption is `V(z) = mask − C_Ψ(z) + Σ_c pad_c(z)`, where `pad_c(z) ≈ s_c S^{(c)}_z a^{(c)}_h`
if `∏_i m^{(c)}_{i,z_i} = 1`, and a noise term otherwise. A **cube program** for the prefix `p`
(length `ℓ`) has `m_{i,b} = [b = p_i]` for `i ≤ ℓ` and `1` afterwards.

**ZF_Ψ(c, j, b; Δ).** Let `G` be an APG hybrid in which slot `c` has `m^{(c)}_{j,b} = 0`, and
let `G'` be `G` with `m^{(c)}_{j,b} := 1`. Let `Δ` be the set of strings whose slot-`c` product
becomes `1`. The claim is `G ≈_c G'` under LWE, uniformly over the adversary's choice of `Ψ`,
under one of two side conditions:

* **(cover)** every `z ∈ Δ` is padded in `G` by another slot;
* **(point)** `Δ = {k}` with `C_Ψ(k) ≠ 0`.

**PM from ZF.** Siblings `Q_0 = p0∗` (slot `c_0`) and `Q_1 = p1∗` (slot `c_1`), with `ℓ = |p|`:

1. `ZF(c_0, ℓ+1, 1; Q_1)` under (cover by `c_1`), so that `c_0` carries `p∗`;
2. the reverse of `ZF(c_1, ℓ+1, 1; Q_1)` under (cover by `c_0`), so that `c_1` has product
   `0` everywhere;
3. a noise-only renormalisation of the dead program of `c_1` into the canonical zero program.
   No `V(z)` changes beyond noise, so this step is covered by §5.

**PI from ZF.** Write the zero program as `[b = k_i]` for `i < h` and `0` at level `h`. Then PI is
`ZF(c, h, k_h; {k})` under (point).

**Faithfulness.** Like TSR_Ψ of `pq-we-two-sided-lwe` §1, `ZF_Ψ` is falsifiable, and it is
independent of the WE statement because `Ψ` is the adversary's choice. Any proof of PM or PI that
does not inspect `Ψ` proves `ZF_Ψ`, and conversely. No new open node is added: PM and PI have
not been registered as nodes, and the statement above is their common, exact form.

## 2. How CVW18 crosses zeros, and why APG cannot

The proof of CVW18 Thm 5.7 / Cor 5.9 (ePrint 2018/360, §5.4, read from the full text) has two
phases:

* **Phase 1, leaf-first (Lemma 5.10).** The bottom `S`-block rows `A̲_i` are taken as LWE secrets,
  with the short `S_{i,b}` as public matrices, so that `S_{i,b}A̲_i + E` becomes uniform. Before
  `A̲_{i−1}` can serve as a secret, Lemma 4.1 removes it from the preimage sampling of level `i`,
  and Lemma 4.1 **requires the targets of those rows to be uniform on both children**.
* **Phase 2, root-first (Lemma 5.11 via Lemma 4.4).** Once only the program rows remain,
  `A_{j−1}^{-1}(M_{j,b}A_j + E) ≈ D_{Z,σ}` holds for an **arbitrary** `Z = M_{j,b}A_j`, including
  zero rows. The condition is that `A_{j−1}` be hidden and needed nowhere else. That holds
  root-first because `J·A_0`, with `J = (J' | I_n)`, is uniform thanks to the `S`-block.

So CVW18 crosses zero entries in phase 2, never in phase 1.

**APG slot rows meet neither condition.** Let `0 ≤ j−1 < ℓ` and `a := a^{(c)}_{j−1}` on the
prefix `p` of slot `c`.

* *Phase 1 fails.* The child `1 − p_j` has target `E`, not uniform. In the dual form, which
  takes `S^{(c)}` as the secret and `a` as the public matrix, the reduction must produce the zero
  child `D` with `a D = E`, and `Hints.zero_row_hint_exposes` (with #108's `zero_entry_hint`)
  then shows `(S a + E')D` is short. So the reduction can decode its own challenge.
* *Phase 2 fails.* The values `V(z)` for `z ∈ p∗` contain `s_c S^{(c)}_{z≤j−1} a`, and `u_O − u_C`
  exposes the row combination `r = (J'_O − J'_C)·Ā_0`. It contains the slot start `a^{(c)}_0`
  (#108 §6, "rank of the left vectors"). So `a` is reachable from a public row and is not hidden.
  Starting phase 2 at the root instead (making `D_{1,b}` Gaussian given `r`) turns the exposed
  reading into a uniform `U·D_{>1}` on **every** string. That is the full WE security statement,
  not a local hop.
* *Live departures cannot be avoided.* By `departure_first_difference`, the departure cubes
  `p_{<j}(1−p_j)∗` of the zero entries of `p∗` partition the complement of `p∗`. They are all
  padded only when everything outside `p∗` is padded, i.e. only in the last hybrid. In the
  lexicographic walk, the zero entries at positions with `k_j = 0` have live departures
  (strings `> k`).

Hence **every local proof of ZF needs a third kind of step**: one that crosses a zero child of a
row that is root-reachable through an exposed combination. The angles below test the candidates
for that step.

## 3. Angle (1): lossy / statistical arguments

**Try.** Put the parent rows `a = a^{(c)}_{j−1}` in lossy mode `a = B C + F` (`B ∈ Z_q^{n'×k}`,
`k < n'`), so that the leaving strings' contribution `s S a + e` depends on `s S` only through
`s S B`. Hide that statistically, flip the entry, and switch back.

* **A matrix under which preimages are sampled is never lossy.** GGH15 needs preimages under
  `A_{j−1}` (all of its rows, including `a`). With an exact trapdoor `A K = 1`, `s ↦ sA` is
  injective and `(sA + e)K = s + eK` decodes (`trapdoor_not_lossy`). The gadget form `A K = G`
  behaves the same way, decoding with `G^{-1}`. So a reduction that samples `D_{j,·}` cannot hold
  `A_{j−1}` in lossy mode.
* **A lossy matrix built with a kernel of its secret part self-defeats.** Suppose the reduction
  knows `K` with `C K = 0`, which is the only way it can sample anything useful under `BC + F`.
  Then `(BC + F)K = F K` is short (`lossy_kernel_approx_trapdoor`). That is the zero-child
  situation, and any LWE challenge it embeds along `a` is decoded by `K`
  (`Hints.zero_row_hint_exposes`).
* **A lossy matrix that is never inverted is already handled.** If the reduction does not sample
  `D_{j,·}` (they come from a challenge), then `A_{j−1}` is hidden and unused, which is exactly
  Lemma 4.4's hypothesis. Lemma 4.4 crosses any zero there with no lossiness. The obstruction is
  not the zero. It is that `a` is root-reachable (§2), and lossiness of `a` does not change
  reachability.
* **A lossy slot is a narrower slot.** For targets `S_j a_j + E` to stay near the column space of
  a rank-`k` `B_{j−1}`, the whole chain must satisfy `S_j B_j ≈ B_{j−1}·(·)`. Then the slot is a
  width-`k` slot plus noise. Switching between rank `k` and full rank is itself a slot hop of the
  same kind, so nothing is gained.

**Self-defeat check.** #84's decoded-defect attack needs two zero children and more than `k + 1`
prefixes at the cut. A slot row on `p` has one zero child and one non-zero prefix reading, so the
attack itself does not apply. Its one-zero-child analogue (§7) applies to every reduction above,
whether it uses a trapdoor or lossiness. **Outcome: closed negatively.**

## 4. Angle (2): Hint-LWE, k-LWE, LWE with side information, entropic LWE

**Try.** The leak `(S a + E')D = S E + E'D` (with `D = D_{j,1−p_j}` and `a D = E`) is a linear
function of the secret–error pair `(S, E')`. Phrase the hop `Y := S a + E' → U` as LWE given that
hint.

* **The hint is the sample.** `D` is a public ciphertext component and is invertible mod `q`
  with overwhelming probability. So `Y = (S E + E'D) D^{-1}` (`zero_child_target_determined`), and
  `H = S E + E'D` and `Y` determine each other. Hint-(M)LWE (Kim–Lee–Seo–Song, CRYPTO 2023; we did not locate a separate "Kim–Lee–Wu" variant: hints
  `γ s + y`, `γ e + z` with fresh Gaussian `y`, `z`) and LWE with side information
  (Dachman-Soled–Ducas–Gong–Rossi, CRYPTO 2020: perfect, modular, approximate and short-vector
  hints) both model hints that leave `Y` partly unpredictable. Here the hint has rank
  `n'·m = dim E'`, with no fresh noise, so the residual problem is the original one.
  * The only remaining secret is `S` behind the public-to-nobody matrix `a = E D^{-1}`. That is
    "LWE with an NTRU-shaped public matrix whose trapdoor `D` is public", and `Y D` short
    distinguishes it.
  * k-LWE (Ling–Phan–Stehlé–Steinfeld) gives short vectors orthogonal to *hidden* directions.
    Here the short object `D` must be published.
* **What a valid hop must preserve.** For the leaving strings to stay dead, any replacement `Y'`
  must keep `Y' D` short, i.e. `Y' ∈ Short·D^{-1}`. Then `Y'` is again a function of a short
  matrix. So the honest hop is a change of the **short** matrix `H`: a statistical or NTRU-type
  statement about `H D^{-1}`, never an LWE step on `Y`.
* **Entropic / lossy LWE (Brakerski–Döttling).** These need a secret with entropy given the view
  and a uniform (or lossy) public matrix. The public matrix `a = E D^{-1}` is neither: with `D`
  public, `a` is a function of a short `E`. With `a` hidden, entropy is not the issue. The
  exposure of §2 is.
* **Parameters.** Even ignoring the above, TLWE-type statements need `σ_{E'}σ_D ≳ q·m`
  (`pq-we-tlwe-masked-ggh15-leaf`). Then the "dead" contribution `E'D` of the leaving strings is
  uniform, i.e. they are padded. On live strings this breaks correctness
  (`TwoSided.decryption_recovers_noise`).

**Outcome: no hinted assumption from the literature gives the hop.** Every local statement about
`(Y, D)` is the identity above or is false. This agrees with `pq-we-hinted-lattice-assumptions`
§2 and refines it: one zero child already suffices.

## 5. Angle (3): flooding only on the leaving strings

**Try.** Use a re-randomisable pad slot to add flooding noise only to the strings that depart at
the zero entry, so that the change of that entry is hidden.

* **Flooding hides short shifts only.** For uniform noise on a window of width `B`, a shift `t`
  costs statistical distance `t/B` (`shift_overlap_card`). For Gaussians the bound is
  `O(t/B)` (CVW18 Lemma 3.2).
  * Any proof of ZF passes through a hybrid where the parent target `Y` is uniform (§2). There
    the leaving strings' term `Y D D_{rest}` is uniform, not short.
  * Hiding that shift needs `B > q`. The leaving strings are live, so flooding them at width `q`
    randomises `V(z)` and breaks correctness on true statements.
* **A temporary pad on the leaving strings is a zero in disguise.** A pad that is added and later
  removed with no net change must cancel exactly. Two slots that cancel on a set have a zero
  child in the difference basis (`copy_state_zero_child`). So the temporary pad has its own zero
  entry, and its own departures are live.
* **Where flooding does help.** The noise-only hops, step 3 of PM (§1), change `V(z)` only by
  noise. Flooding them with `2^λ·B_noise` costs `+λ` bits in `log q`. At `λ = 128` and
  `log q ≳ L·log₂√m ≈ 4224·19 ≈ 2^{16.3}` (#108 §7) that is under `1%` of `log q`, so the
  ciphertext stays about `2^{97}` bits.

**Outcome:** flooding pays for the renormalisation hops and nothing more.

## 6. Angle (4): minimal scheme changes

* **(4a) Random low-rank shift on zero entries, cancelling along witness paths.** The slot
  enters `V = O − ck` only through the start-weight difference `(w_O − w_C)` at the root. Both
  readings share every later level and the sink. So the slot's contribution to `V(z)` is
  `(w_O − w_C)·s_c S_z a_h^{state(z)}`, and it cannot depend on whether `z` is a witness. Making
  it vanish on leaving strings needs `a_h^{state} ≈ 0` for their final state: a zero at the sink.
  The cancellation therefore cannot be routed through the two left vectors.
* **(4b) A fresh LWE level after each zero entry / a dead state.** Replace each zero by a move
  into a dead state with its own rows and live targets.
  * The dead state must vanish at the sink (`a_h^{dead} = 0`). Dead rows at level `h − 1` then
    have **two** zero children, which is the shape of #84's decoded defect.
  * Leaf-first phase 1 now stops at the sink, because every row that feeds the dead state is
    stuck. Phase 2 is still blocked by the exposure.
  * By `first_zero_step`, every pad that vanishes on some string has, along that string, a first
    level where a non-zero row combination meets a zero child. Inserting levels only moves that
    level.
  * Cost: one extra row block per slot (`+n'` rows of `m` columns, under `1%` of the
    ciphertext). No proof is gained.
* **(4c) Permutation counters (mismatch count mod `ℓ + 1`) or a copy of the mask state.** These
  programs have no zero entries, but the accept vector must vanish on the non-cube states (4a).
  For the copy state, the departing transitions of the copy and main rows share the target
  `R_j A^{main}_j`, so the difference row `a^{copy} − a^{main}` has a zero child
  (`copy_state_zero_child`). The copy-state design is APG (and the MP2 comparator chain) in
  another row basis, and zero entries are basis-invariant.
* **(4d) Prefix trees that share the prefix rows of sibling slots.** This removes the duplicated
  prefix zeros of `c_0` and `c_1`, but not the shared ones. By `departure_first_difference`,
  those zeros have live departures.

**Outcome:** no redesign removes the crossing. All of them keep APG's cost, `≈ 2^{97}` bits.

## 7. Cross-check against the decoded-defect attack and its one-child analogue

* **Attack on ZF itself: none found.** The values that change lie in `Δ`, and `Δ` is padded
  (cover) or a single string (point).
  * The decoded-defect statistic (`TwoSided.decoded_defect_attack`) needs two zero children of
    one row and more than `k + 1` prefixes with non-zero reading.
  * A slot row on `p` has one zero child, and only the prefix `p` reads it with a non-zero
    coefficient (all other prefixes departed earlier).
  * The two-child consistency obstruction (`TwoSided.two_child_preimage_consistency`) is vacuous
    for one structured target.
  * So ZF is consistent with every attack in the DAG.
* **One-zero-child self-defeat (for reductions, not for the scheme).**
  * Suppose a reduction embeds an LWE-type challenge in the parent target `Y` of a zero child
    and must itself output the zero child `D`. Then it can compute `Y D`, which is short in one
    case and uniform in the other (`Hints.zero_row_hint_exposes`), so its challenge is easy.
  * This covers taking `S^{(c)}` as the secret, lossy parents (§3), and preimage-first sampling
    of the zero child, which gives `a = E D^{-1}` (`FlipShift.one_zero_child_explains`).
  * The only reductions left are those whose zero child comes from the challenge with the parent
    hidden, i.e. Lemma 4.4. §2 shows Lemma 4.4 cannot start below an exposed root row.

## 8. The remaining gap, stated once

**Lemma 4.4 with one exposed root row (L4.4-r).** Let `A_0` have rows `[r-part; rest]`, where
the single combination `r = w·A_0` is public. Let `D_1 ← A_0^{-1}(Ŝ_1 A_1 + E)` for a γ⊗ level
whose rows have zero children. The question is when `D_1`, given `r`, can be replaced by a
preimage whose **non-`w` directions** are Gaussian, while `r D_1` keeps its law. In other words,
can phase 2 run on the orthogonal complement of the exposed row?

* PM and PI need exactly this for the slot rows on `p`. MP2's `ML_i` needs the two-zero-child
  version.
* It is the rank-one-difference condition of `pq-we-witness-prf-masked-evaluator` §5 (attack 2)
  turned into a proof obligation.
* We do not know a proof, and the zero-entry identities do not refute it: `r` reaches the slot
  rows only through the live child chain, never through a zero child.
* Suggested next step: test L4.4-r on the smallest case, a single slot with `ℓ = 1`, one mask
  block and no constraint block, where `r = A_0^{mask} + a_0^{(c)}`. Check whether a Bonsai split
  (CVW18 Lemma 4.4's proof) along `w^⊥` keeps `r D_1` exact.

**Cost.** Unchanged. If L4.4-r (two-child form for MP2, one-child form for APG) were proved, APG
would be a complete WE at `≈ 2^{97}` bits (`< 2^{100}`, PR #105). Its LWE premise would be
`≈ 400` bits, from `2^{129}` ZF hops plus internal hops (#108 §6), with `+λ` in `log q` for the
flooded renormalisation hops (§5).

## 9. Formal results (Lean, complete proofs)

| Theorem | Content | Used in |
| --- | --- | --- |
| `ZeroCross.zero_child_target_determined` | `A D = E`, `D Dinv = 1` ⇒ `S A + E' = (S E + E' D) Dinv` | §4 |
| `ZeroCross.trapdoor_not_lossy` | `A K = 1` ⇒ `s ↦ sA` injective and `(sA + e)K = s + eK` | §3 |
| `ZeroCross.lossy_kernel_approx_trapdoor` | `C K = 0` ⇒ `(B C + F) K = F K` | §3 |
| `ZeroCross.copy_state_zero_child` | equal targets up to noise ⇒ the difference row has a zero child | §5, §6 |
| `ZeroCross.shift_overlap_card` | `t ≤ B` ⇒ `#([0,B) \ [t,t+B)) = t` (flooding distance `t/B`) | §5 |
| `ZeroCross.first_zero_step` | `f 0 ≠ 0`, `f h = 0` ⇒ there is `j < h` with `f j ≠ 0` and `f (j+1) = 0` | §6 |
| `ZeroCross.departure_first_difference` | outside a prefix cube ⇔ a first difference below the prefix length | §2, §6 |

---
title: WE - APG' widths redone - CVW18 leaf-first steps need pad width of order (log q)^2, rings fail and modules only shrink size, n cube slots are forced; APG' stays above 2^100
refs: [definition:WE_CircuitSAT, definition:WE_CircuitSAT_Capped, definition:GGH15, definition:WE_MaskedGGH15, note:pq-we-native-hop-designs, note:pq-we-multipass-ggh15, note:pq-we-hybrid-count-barrier, theorem:AdvancedEncryption.WE.NativeHop.lex_prefix_cubes, theorem:AdvancedEncryption.WE.RingGGH15.ring_kernel_break, theorem:AdvancedEncryption.WE.RingGGH15.module_adjugate_break, theorem:AdvancedEncryption.WE.PadSlots.point_complement_cover_card]
tags: [witness-encryption, ggh15, parameters, barrier, open-problem]
---
Design-AI sub-task (ss) on `Def_WE_CircuitSAT_Capped` (cost `N ≤ 2^{100}` TM steps, which also
bounds the ciphertext bits). The object is the additive-pad masked γ⊗-GGH15 WE with shared pad
secrets, "APG'", of open PR #111 (note "pq-we-exposed-root-reachable-lemma"), built on APG of
`pq-we-native-hop-designs` §6. Open PRs are cited by number only. Following the project owner's
decision, the parameters are given for **APG'-direct**: no CPRF block and no left vectors
`u_O, u_C`. The single public left vector is the exposed row `R = P A_0` (mask rows plus shared
pad rows). Decryption reads `R D_w = mask + constraint + noise`, and the ciphertext is
`⌊mask⌉ + μ`. #111's view after the CPRF block is removed is exactly this.

PR #111 found that the pad leaf-first steps need a wide pad block, and it estimated APG' at
`2^{108}`–`2^{110}` bits. Its suggested repairs were ring/module levels and fewer pad slots. This
note checks those repairs, recomputes all parameters with a script, and proves three exact
sub-lemmas in Lean.

CVW18 = Chen–Vaikuntanathan–Wee, ePrint 2018/360, read from the full text (Lemmas 3.8, 3.9, 4.4,
5.10, Thm 5.7, Cor 5.9, Remark 7.2). The three theorems below have complete Lean proofs (Mathlib
only). Everything else is an argument checked step by step by the submitting agent, plus a
parameter script.

## 0. Answer

1. **#111's width correction is still too small** (§1). CVW18's leaf-first step (Lemma 5.10)
   and APG''s CC step 2 use LWE with a *short public* matrix: `LWE_{n',2n',q,U,D_σ,D_σ}`. The
   secret is the uniform rows of `A_i`, and the γ⊗ secrets `S_{i,0}, S_{i,1}` are public. CVW18
   gets this from standard LWE only through Lemma 3.9 (BLMR13), which needs
   `n' ≥ 2 n_std log q`. Remark 7.2's `n = Ω(λ log q)` is that bound with `n_std = λ`.
   * At the faithful level, `n' ≈ 2^{35}`–`2^{41}`, not `2^{22.5}`.
   * There is also a direct attack. A dense-sublattice version of #111's kernel break, using
     LLL, breaks the step in polynomial time unless `n' ≳ ρ² / log₂(σ_S √n')`, where
     `ρ = log₂(q/σ_E)` (§2).
2. **The role reversal cannot be avoided in APG'** (§1). The pad secret is shared by all slots,
   and the other slots' rows keep their trapdoors. So the reduction must know `S`.
3. **What lowers ρ** (§3). We cannot give the pad block a smaller modulus. But two changes help:
   * put the 128 walked levels *last* (leaf side);
   * set the pad secrets to `I` on the other levels.

   The pad noise can then be wide, and `ρ_pad ≈ 128·log₂ m + λ_s` (about `6.1·10^3`) instead of
   `log q` (about `2^{17.7}`).
4. **Rings fail and modules only cut the size** (§2, §4).
   * Over a commutative ring with module rank 1, the leaf-first step is broken at every ring
     degree (`ring_kernel_break`).
   * At module rank `k`, an explicit adjugate kernel vector (`module_adjugate_break`) forces
     `k ≳ ρ / (2 log₂(σ√(dk)))`.
   * The integer dimension `dk` must still clear the thresholds of item 1. Modules divide the
     size by the ring degree `d`, but not the width.
5. **Fewer pad slots are impossible for cube slots** (§5). Covering all strings but one needs
   `n` subcubes (`point_complement_cover_card`). Every single-point-insertion walk passes through
   that hybrid, so `w ≥ n = 128` in every order.
6. **Numbers** (§6, script). APG'-direct, smudging `λ_s = 276` or `422` (§7).
   * **Integer GGH15:**
     * proof-backed (Lemma 3.9 as stated): best size `2^{128}`;
     * the variant assumed directly (heuristic): `2^{114}`;
     * attack-only widths: still `2^{103}`.
   * **Module GGH15** (unproved module premise):
     * heuristic: size `2^{100.5}`, work `≈ 2^{114.5}`;
     * proof-backed modulo the module lemma: `2^{109}`.
   * **APG' does not meet `2^{100}`.** Within this design (γ⊗ / shared-secret leaf-first steps,
     CVW18 trapdoors, cube pads) the integer version is impossible even at attack-only widths
     (`2^{103}`).
   * Dropping the CPRF block (APG'-direct) saves `< 0.1` bit.

## 1. The leaf-first step is LWE with a short public matrix

**What CVW18 proves.** Lemma 5.10 (the step `1.(i+1) → 1.i` of Thm 5.7) replaces the S-rows of
the level-`i` targets by uniform. In the paper's words, it "follows Lemma 3.9, by treating `A_i`
as the LWE secret, and `S_{i,0}, S_{i,1}` as the public matrices". The assumption is
`LWE_{n,2n,q,U(Z_q),D_{Z,σ},D_{Z,σ}}`: the secret is uniform of dimension `n`, and the public
matrix `[S_{i,0}; S_{i,1}]` (`2n × n`) is Gaussian.

* Lemma 3.9 (LWE with small public matrices, BLMR13): `LWE_{n_0,m,q,U,D_σ,D_σ}` is as hard as
  standard `LWE_{n,m,q}` for `n_0 ≥ 2 n log q`.
* Remark 7.2 sets `n = Ω(λ log q)` "due to Lemma 3.9 and Lemma 3.8". That is
  `n_0 = 2 n_std log q` with `n_std = λ`, which is valid under the paper's sub-exponential
  setting `q ≤ 2^{λ^{1−ε}}`.
* With concrete parameters, `n_std` is the standard-LWE dimension for modulus `q` at the premise
  strength. Here `log q ≈ 2^{17.7}` and the strength is `λ' ≈ 128 + 2·log₂(hops) ≈ 422`.
  * The estimator mirror (`python/lwemodel`, primal uSVP) gives `n_std ≈ 2^{21.4}`.
  * So `n' ≥ 2^{1+21.4+17.7} ≈ 2^{40}`.
* #111 §6 took `n' ≈ λ log q / 7.2`, which is `n_std`, and so missed the factor `2 log q`.

**Why APG' cannot avoid the role reversal.** In CC step 2 of #111 the pad secret `S_{L,b}` is
shared by every slot active at `(L, b)`. Those slots' rows of `A_L` still carry trapdoors, which
are needed for the level-`L+1` preimages.

* Normal-form LWE with secret `S_{L,b}` would need those rows as the challenge's public matrix.
  The reduction then has no trapdoor for them, so it cannot sample the level-`L+1` preimages.
* It also cannot compute `S_{L,b} a^{(c')}_L + E` itself without knowing `S`.
* The same holds in CVW18's γ⊗ form. `M ⊗ S` and the `S` block share `S`, which is why Thm 5.7
  gives `S` to the adversary as auxiliary input ("S-dependent security").
* So every shared-secret leaf-first step is a small-public-matrix LWE step.

**Which steps are not affected.**

* Blocks with unshared secrets can use normal-form LWE with `n = n_std`. This is the CPRF block
  of APG' (now dropped) and the mask block (bit-independent `R_i`, also unshared).
* #111's L4.4-S steps and CVW18 Lemma 4.4 use `LWE_{m_1,·,q,U,D_σ,D_σ}` with
  `m_1 ≥ 2 n log q` (`n` = all rows), which is satisfied once the total row count `N ≥ n_std`.

## 2. The kernel break, sharpened, and its ring and module forms

**Dense-sublattice break (integers).** The setting:

* Public `S ∈ Z^{M×n'}` with entries of width `σ_S`.
* Samples `y = S a + e mod q`, with `a` uniform and `‖e‖ ≤ B_e`.
* Write `ρ = log₂(q/B_e)`.

Pick `r ≥ 1` and keep `n' + r` rows `S_r`.

* The lattice `Λ_r = {z ∈ Z^{n'+r} : z S_r = 0}` has rank `r`. Its determinant is at most the
  covolume of the column lattice of `S_r`, which by Hadamard is at most `(σ_S √(n'+r))^{n'}`.
* LLL finds `z ∈ Λ_r` with `log₂ ‖z‖ ≤ (r−1)/4 + (n'/r)·log₂(σ_S √(n'+r))`.
* Then `z y = z e mod q` (#111's identity `phase_one_kernel_break`). This is short whenever
  `log₂ ‖z‖ + log₂ √(n'+r) < ρ − 2`, while `z y` is uniform for uniform `y`.

Minimising over `r` (at `r ≈ 2 √(n' L_S)`, with `L_S = log₂(σ_S √n')`) gives:

* **polynomial-time break when `n' ≲ ρ² / L_S`** (rigorous LLL constant);
* break by BKZ-`β` when `n' ≲ ρ² / (4 L_S log₂ δ_β)`.

At the premise level (`β ≈ 1495`, `log₂ δ ≈ 0.00216`), the second bound is the heuristic width of
tier H in §6.

#111's exact-kernel threshold `n' log₂(σ√n') > log₂ q` is the case `r = n'`. It is too weak by a
factor of about `ρ / L_S`.

*Toy check* (script `toy_kernel.py`, exact-rational LLL on `[I | K S]`, `σ_S = 3`):

| `n'` | `r` | shortest kernel `z` (log₂) | dense-sublattice bound (log₂) | Hadamard scale (log₂) |
| --- | --- | --- | --- | --- |
| 10 | 4 | 7.3 | 9.5 | 34.9 |
| 14 | 5 | 8.7 | 11.4 | 51.9 |

**Rings (module rank 1): broken at every degree.** The ring analogue of CVW18 Lemma 5.10 gives
the public `s_0, s_1 ∈ R` and the samples `y_b = s_b a + e_b`. Then
`s_1 y_0 − s_0 y_1 = s_1 e_0 − s_0 e_1` (`ring_kernel_break`), which is short. So ring GGH15 with
public secrets ("Ring-LWE with small public elements") is false for every ring degree. A
ring-GGH15 proof of APG' needs a different premise for this step, and none is known.

**Modules (rank `k`).** With `S_0, S_1 ∈ R^{k×k}`, set
`z_0 = det(S_1) (u adj S_0)` and `z_1 = det(S_0) (u adj S_1)`. Then
`z_0 y_0 − z_1 y_1 = z_0 e_0 − z_1 e_1` (`module_adjugate_break`).

* The entries are products of `2k − 1` secret entries, so this needs no lattice reduction. It
  breaks the step when `2k log₂(σ_S √(dk)) ≲ ρ`.
* The `Z`-lattice attacks above apply to the integer dimension `dk`.
* So a module pad needs rank `k ≳ ρ / (2 log₂(σ_S √(dk)))` **and** `dk` above the integer
  threshold.

**Do the other proof steps survive over modules?** The basis change (`W⁻¹` with entries in
`{0, ±1}`), the Bonsai split (CVW18 Lemma 3.13), Gaussian preimages (Lemma 4.1, using module
trapdoors), smudging, and #111's `cover_pad_card` (over any finite ring) are algebraic or
statistical, and they carry over.

* The *premise* does not carry over automatically. The module analogue of Lemma 3.9 needs a ring
  leftover-hash (regularity) lemma. It is plausible but not in CVW18, and it is not proved here.
* So a module APG' needs either that lemma (proof-backed tier) or the directly assumed
  small-public-matrix MLWE (heuristic tier).
* Ring/module GGH15 also carries extra algebraic structure (determinants and norms are
  multiplicative over products). It needs its own cryptanalysis.

## 3. A smaller modulus for the pad block: no; a smaller ρ: yes

* **No separate modulus.** The pad rows share the preimages `D_{i,b} = A_{i-1}^{-1}(·)` with
  every other block, and all readings are mod `q`.
  * Pad noise at level `i` is multiplied by `D_{i+1} ⋯ D_h`, which grows by about `log₂ m` bits
    per level with CVW18's `σ ≥ 2√(n log q)`, `m ≥ 4 n log q`.
  * So `log₂(q/σ_E) ≥ (h − i) log₂ m` at that level.
  * Modulus switching rescales `q` and `σ_E` together and leaves `ρ` unchanged.
* **Reordering.** A γ⊗ diagonal (CNF) program, a pad cube and a bit-independent mask all commute
  across levels. So the order of levels is free.
  * Put the `n = 128` walked levels last.
  * Choose the pad noise per level as wide as correctness allows:
    `σ_E^{pad}(L) ≈ q / (2^{λ_s+20} · m^{h−L} · growth_S)`.
* **Identity pad secrets off the walk.** Set `S^{pad}_{i,b} = I` on the non-walked levels, where
  every pad entry is `1`.
  * There a slot target is `a_i + E` with `a_i` freed, which is already uniform. That
    leaf-first step needs no LWE (a one-time pad).
  * The co-location and short-lift properties of #111 §3 hold with `S = I`.
* **Effect.** For the role-reversed steps, `ρ_pad ≈ 128·log₂ m + λ_s + 20 ≈ 6.1·10^3`, against
  `ρ = log q ≈ 2^{17.7}` before. This is the largest saving available. It changes the scheme (level
  order, identity pad secrets, per-level pad noise), so the attacks of
  `pq-we-native-hop-designs` §6 and of #111 must be re-checked on the reordered program. The CC,
  PM and dead-slot proofs of #111 are unchanged, since they never use the level order.

## 4. Multi-bit levels

Reading `k_b` bits per level (`2^{k_b}` branches) reduces the level count to `⌈4224/k_b⌉`, and
`log q` with it. The pad entries become indicators of digit sets, so bit-prefix cubes are still
width-1 slots.

Each CC flip at a digit level becomes several flips, one per digit value. CC, PM and
`lex_prefix_cubes` must be restated for the larger alphabet. The proofs look unchanged but are
not redone here.

## 5. Fewer pad slots: impossible with cube slots

* A width-1 diagonal `0/1` slot pads the subcube `Π_i {b : m_{i,b} = 1}`.
* #111's walk inserts one point per PI. Inserting a point needs `C_Ψ(k) ≠ 0` at that point, so
  without a witness the walk reaches the hybrid where all strings but the last are padded.
* `point_complement_cover_card`: any family of subcubes that avoids a point `p` and covers
  `{0,1}^n \ {p}` has at least `n` members. (The neighbour `p ⊕ e_i` can only be covered by a cube
  that fixes coordinate `i` against `p`, and such a cube contains no other neighbour.)
* So **every** insertion order needs `≥ n = 128` simultaneous cube slots, and #111's `n + 1` is
  optimal up to one.
* `O(1)` slots would need non-cube pads, for example a width-3 comparator program for `[z < k]`.
  That is MP2's threshold walk, whose reroute `t → t+1` has no proof (`pq-we-multipass-ggh15`
  §4).

## 6. Recomputed parameters (APG'-direct)

**Model** (script `apg_params.py` + `grid.py`, sub-task scratch).

* **Levels.** `L = 128 + 4096 = 4224` bit-levels, read `k_b` bits per level. That gives
  `L' = ⌈L/k_b⌉` levels with `2^{k_b}` branches each.
* **Trapdoors** (CVW18 Lemmas 3.10, 3.11, 4.4). `m = 4 N log q` (integer dimension) and
  `σ_D = 2√(N log q)`, so the noise grows by about `log₂ m + 1` bits per level, and
  `log q = L'(log₂ σ_D + ½ log₂ m + 1) + λ_s + 20`.
* **Widths.**
  * `w = n + 1 = 129` pad slots, each of integer width `n'`.
  * A mask block of width `n_std(log q)` (normal form).
  * `3·2^{12}` clause positions of width `max(2^{10}, d)`.
  * No CPRF block.
* **Premise.** `λ' = 128 + 2(135 + log₂ L')` (#111 §6 rule); `n_std` from the estimator mirror.
* **Ring degree.** `d` (`d = 1` is integer GGH15). The pad module rank `k` satisfies §2's
  adjugate bound.
* **Pad width `n'` by tier.**
  * P: `2 n_std(ρ_pad) log q` (Lemma 3.9 as stated).
  * PM: `2 n_std(ρ_pad) ρ_pad` (Lemma 3.9 after modulus switching; a sketch, not proved).
  * H: `ρ_pad² / (4 L_S log₂ δ_{λ'})` (the variant assumed directly; BKZ estimate).
  * A: `ρ_pad² / L_S` (attack-only: just outside the polynomial-time LLL break; not a secure
    choice).
* **Size.** `L'·2^{k_b}·m²·(log₂ σ_D + 3.5)/d` bits (the preimages `D`).
* **Work.** Size plus MP12 preimage sampling. With fast matrix multiplication
  (`ω = 2.373`) for `D = R Z`, the sampling costs about `L'·2^{k_b}·(m/d)^{ω}·d log d`.
  Schoolbook sampling is about 18 bits more.

**APG'-direct, `k_b = 1`, `d = 1` (log₂ values, `λ_s = 276`).**

| Tier | walked levels | `log₂ log q` | `ρ_pad` | `n'` | `N_rows` | `m` | size |
| --- | --- | --- | --- | --- | --- | --- | --- |
| A | as #111 | 17.95 | 253791 | 32.0 | 39.1 | 59.0 | 136.1 |
| H | as #111 | 18.11 | 283662 | 39.0 | 46.0 | 66.1 | 150.4 |
| P | as #111 | 18.15 | 291498 | 40.8 | 47.8 | 67.9 | 154.2 |
| A | last | 17.66 | 5990 | 21.2 | 28.3 | 48.0 | 113.8 |
| H | last | 17.85 | 6018 | 27.8 | 34.9 | 54.7 | 127.4 |
| P | last | 18.03 | 6046 | 35.1 | 42.1 | 62.1 | 142.4 |

**Best over `k_b ∈ {1,4,8,12,16}`, `log₂ d ∈ {0,8,…,20}`, walked levels last.** At `λ_s = 276`;
`λ_s = 422` adds `0.3`–`0.5` bits.

| Tier | `k_b` | `log₂ d` | `k` | `log₂ log q` | `ρ_pad` | `n'` | `N_rows` | `m` | **size** | work (fast MM) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| A (integer) | 8 | 0 | – | 14.45 | 953 | 15.9 | 24.3 | 40.8 | **103.2** | 116.8 |
| H (integer) | 8 | 0 | – | 14.62 | 956 | 22.5 | 29.6 | 46.2 | **114.1** | 129.6 |
| P (integer) | 8 | 0 | – | 14.82 | 959 | 29.2 | 36.3 | 53.1 | **128.1** | 146.0 |
| A (module) | 8 | 10 | 62 | 14.45 | 953 | 16.0 | 24.3 | 40.8 | **93.2** | 106.4 |
| H (module) | 8 | 16 | 111 | 14.66 | 1052 | 22.8 | 30.7 | 47.4 | **100.5** | 114.5 |
| PM (module) | 8 | 18 | 103 | 14.71 | 1085 | 24.7 | 32.6 | 49.4 | **102.6** | 116.6 |
| P (module) | 8 | 20 | 715 | 14.83 | 1119 | 29.5 | 36.7 | 53.5 | **109.0** | 123.9 |

**Reading.**

* **Integer GGH15 (no new premise):** even the attack-only widths give size `2^{103}`.
  Proof-backed, the best is `2^{128}` (`N ≥ 2^{128}`). Within integer APG' this is a barrier,
  not a missing optimisation: in the A tier the width is set by the `3·2^{12}` clause positions
  (about `2^{23.6}` rows) and the trapdoor `m ≥ 4 N log q`, not by the pads.
* **Module GGH15:**
  * Its pad premise (module Lemma 3.9 or the variant assumed directly) is not available today
    (§2).
  * The best heuristic set is H, `d = 2^{16}`, `k_b = 8`, with size `≈ 2^{100.5}` and work
    `≈ 2^{114.5}`, so `N ≈ 2^{114.5} > 2^{100}`.
  * Only the insecure attack-only widths reach size `2^{93}`, and even their sampling work is
    `≈ 2^{106}`.
* **CPRF removal (APG'-direct)** saves `< 0.1` bit. The CPRF block's width `n_std ≈ 2^{21.4}`
  is under 1% of the rows once the pads are wide (rows `2^{28.3}` and up). Against #111's own
  figures (pads `128·2^{22.5}`) it saves about 1%.
* **Which proofs each change touches.**
  * Level reordering and identity off-walk pad secrets change the scheme. CC, PM, the dead-slot
    moves and `cover_pad_card` are order-free and still hold. The attack checks of
    `pq-we-native-hop-designs` §6 and #111 must be redone.
  * Multi-bit levels change the alphabet of CC, PM and `lex_prefix_cubes` (restatement needed).
  * Modules change every LWE premise (module Lemma 3.9 needed) and need a new cryptanalysis of
    the commutative structure.
  * Per-level pad noise changes only the smudging constants.

## 7. Smudging parameter

* #111's L4.4-S steps use CVW18 Lemma 3.2 with `σ_E ≥ 2^{λ_s} ‖G‖ σ_LWE`. Each step loses
  `2^{−λ_s}`.
* There are about `2^{147}` such steps: `2^{135}` macro-hops times up to `L` levels; the `L`
  smudging terms per macro-hop are part of this count.
* So `λ_s ≥ 128 + 147 + 1 = 276` keeps the total statistical loss under `2^{−128}`. Matching the
  per-hop budget of the 422-bit premise needs `λ_s ≈ 422`. Both are computed.
* **Effect.**
  * On `log q`: `+λ_s` bits once, which is `0.2%`–`1.8%` of `log q` (`2^{17.7}` at `k_b = 1`,
    `2^{14.5}` at `k_b = 8`).
  * #111's "`+λ` bits, under 1%" therefore holds at `k_b = 1` even with `λ_s = 422`. It fails
    at `k_b = 8` with `λ_s = 422` (`1.8%`).
  * On `ρ_pad` it is large: `λ_s` is `25`–`35%` of `ρ_pad ≈ 950`–`1270` after reordering. Since
    `n' ∝ ρ_pad²`, it costs about `0.3`–`0.5` bits of size.
  * The tables use `λ_s = 276`.

## 8. Formal results (Lean, complete proofs)

| Theorem | Content | Used in |
| --- | --- | --- |
| `RingGGH15.ring_kernel_break` | `s1 (s0 a + e0) − s0 (s1 a + e1) = s1 e0 − s0 e1` over a commutative ring, `a` in any module | §2 rings |
| `RingGGH15.module_adjugate_break` | with `z0 = det S1 (u adj S0)`, `z1 = det S0 (u adj S1)`: `z0·(S0 a + e0) − z1·(S1 a + e1) = z0·e0 − z1·e1` | §2 modules |
| `PadSlots.point_complement_cover_card` | subcubes avoiding `p` that cover `{0,1}^n \ {p}` number at least `n` | §5 |

## 9. Remaining gap

1. **No APG' parameter set meets `2^{100}`.**
   * Integer APG' is above `2^{100}` even at attack-only widths.
   * Module APG' reaches size `≈ 2^{100.5}` only under an unproved module premise and a
     heuristic width estimate, and its sampling work is still `≥ 2^{114}`.
2. **The obstruction is structural.** Shared γ⊗/pad secrets force small-public-matrix LWE, and
   its secure width grows like `ρ²`. The `L ≈ 4224`-level chain makes `log q`, and therefore
   `m ≥ 4 N log q`, large.
3. **Ways out leave this design.** Each one needs new work:
   * a leaf-first step for shared secrets that uses normal-form LWE;
   * a much shorter chain (fewer than about `2^9` levels);
   * a GGH15 trapdoor with `m = O(N)` and sub-cubic sampling.
4. **PI (point insertion) stays open**, as in #111 §7.

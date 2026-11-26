---
title: Lattice assumptions with hints versus the masked-leak lemma ML_i of multi-pass GGH15 WE - survey, decoding checks and a row-space barrier
refs: [definition:WE_CircuitSAT, definition:GGH15, definition:WE_MaskedGGH15, definition:SuccinctLWE, definition:DecomposedLWE, note:pq-we-multipass-ggh15, note:pq-we-two-pass-reroute, note:pq-we-mp2-cryptanalysis, note:pq-we-equality-cube-flip, note:pq-we-hybrid-count-barrier, theorem:AdvancedEncryption.WE.Reroute.multipass_subtree_hop, theorem:AdvancedEncryption.WE.GGH15.path_identity, theorem:AdvancedEncryption.WE.Hints.zero_row_hint_exposes, theorem:AdvancedEncryption.WE.Hints.rank_condition_necessary, theorem:AdvancedEncryption.WE.Hints.basis_struct_no_zero_row]
tags: [witness-encryption, ggh15, barrier, open-problem, assumption, literature]
---
Design-AI sub-task (hh) on `Def_WE_CircuitSAT` (NAND Circuit-SAT, 128-bit witness, `2^12` gates,
`λ = κ = 128`). The efficient multi-pass candidate MP2/MP3 (`pq-we-multipass-ggh15`, about
`2^97` bits) misses exactly one lemma: the masked-leak lemma `ML_i`, which is the minimal form of
the open node `AdvancedEncryption.WE.Reroute.multipass_subtree_hop` (`pq-we-two-pass-reroute`
§7). Three open PRs (not merged when this note is written, so cited by number) show what a proof
needs:

* #84 (two-sided LWE): the decoded-defect attack;
* #86 (TLWE leaf);
* #90 (equality-cube flip, succinct-shaped levels): one-child integrality, and the fact that
  succinct hints decode every slot.

Together they say: a proof must simulate the downstream witness-carrying levels **without being
able to decode any branch along a common suffix**. Trapdoors, succinct-LWE hints, TLWE,
decomposed LWE and preimage-first sampling all fail this. This note surveys the falsifiable
lattice assumptions "with hints" from the literature and checks each one against that
requirement and against the decoded-defect attack.

The three `Hints.*` theorems have complete Lean proofs. Everything else is an informal argument.

**Answer.**

1. **No assumption in the literature supplies `ML_i` (§3).** All of these fail:
   * BASIS_rand and BASIS_struct;
   * PRISIS and h-PRISIS (the "power" family);
   * ℓ-succinct LWE/SIS;
   * the shifted multi-preimage trapdoor;
   * generalized related-trapdoor LWE;
   * k-LWE and k-SIS;
   * k-R-ISIS, k-M-ISIS and twin-k-M-ISIS;
   * OM-ISIS and ISIS_f;
   * TLWE, decomposed LWE and tensor LWE;
   * (matrix) NTRU.

   Each one either decodes the row it would have to hide, or gives no preimage of a structured
   zero target, or gives preimages only under matrices that avoid the challenge direction. The
   assumptions that do contain zero-target preimage chains (evasive LWE in all its forms, and the
   new assumptions of Root iO and Diamond iO) are excluded. HHSS17's "tags" are not an
   assumption.
2. **A row-space barrier explains why (§2).** Every LWE-provable hint assumption obeys the same
   rule: no hint is a short preimage, under a matrix whose row space contains the challenge
   direction, of a target that is small on that direction. Two Lean theorems show that the rule
   is necessary:
   * `Hints.zero_row_hint_exposes`: such a hint decodes the challenge;
   * `Hints.rank_condition_necessary`: the rank condition of related-trapdoor LWE is necessary.

   `ML_i` needs exactly the forbidden objects: the two children `D_{i+1,b}` are square
   preimages under `A_i`, and their targets are small on the hidden row `δ`. So the challenge
   cannot sit on `δ` alone. It must be padded, and the pad's targets must stay undecodable through
   a continuation that carries witness zeros. Followed level by level, this forces the
   assumption to contain a GGH15 encoding with honest zeros below a planted row. That is TSR_Ψ of
   #84, i.e. the open node itself.
3. **No instantiation, no new definition (§4).** No surveyed assumption works, so MP2's levels
   were not re-instantiated, and nothing was registered as an assumption. MP2 stays a
   conditional `≈ 2^97`-bit candidate. The remaining gap is unchanged: `ML_i` /
   `Reroute.multipass_subtree_hop`.

## 0. The requirement, made precise

From `pq-we-two-pass-reroute` §2 and §7 and #84 §0, the scalar-row model at one chain level `i`
has three parts.

* **Hidden row with two zero children.** `A_i ∋ δ`, with `δ` uniform and hidden, and
  `δ D_{i+1,b} = f_b` small for `b ∈ {0,1}`. The `D_{i+1,b}` are square (`m × m`) Gaussian
  preimages, because every GGH15 level matrix has `m` columns.
* **Masked leak.** `v_t = ℓ^{lt}_i + β δ + c_t A^{con}_i + e`. `ML_i` says that `β = 1` and
  `β = 0` cannot be told apart.
* **Continuation.** Levels `> i+1` are a masked γ⊗-GGH15 encoding with honest zeros along the
  witness completions. Each prefix has its own completions, because of the equality clauses.

A reduction `R` from a hinted assumption must output this view, and it must satisfy:

* **(N1)** `R` cannot decode level `i` (else it reads `β` off `v_t`) or level `i+1` along a common
  suffix (#84 §3; #90, one-child integrality);
* **(N2)** `R` cannot use preimage-first sampling for the two square children (#84, two-child
  consistency);
* **(N3)** the assumption must be falsifiable, statement-independent, post-quantum, and in the
  literature, and it must not be evasive, iO-type or local mixing.

For each assumption below we record:

* **(h1)** under which matrices it gives preimages, public or hidden;
* **(h2)** of which targets, in particular whether some row of a target is small or zero;
* **(h3)** whether the hint decodes the challenge direction, which is the attack check of #84 and
  #90.

## 1. Sources read

* **Read from the full text (author copies, PDFs in the session scratch only):**
  * Wee–Wu, *Succinct vector, polynomial and functional commitments from lattices* (EUROCRYPT
    2023, ePrint 2022/1515): Assumptions 3.2 and 3.3, Theorem 3.4, §6.1, Remark 6.2.
  * Wee–Wu, *Lattice-based functional commitments: fast verification and cryptanalysis*
    (ASIACRYPT 2023): ℓ-succinct SIS, and the attack on knowledge k-R-ISIS.
  * Waters–Wee–Wu, *Multi-authority ABE from lattices without random oracles* (TCC 2022):
    Assumption 4.1 and Theorem 4.2 (generalized related-trapdoor LWE).
  * Waters–Wee–Wu, *New techniques for preimage sampling: improved NIZKs and more from LWE*
    (EUROCRYPT 2025): shifted multi-preimage sampling.
  * Ling–Phan–Stehlé–Steinfeld, *Hardness of k-LWE and applications in traitor tracing*
    (CRYPTO 2014, long version): Definition 15 and Theorem 18.
  * Halevi–Halevi–Shoup–Stephens-Davidowitz, *Implementing BP-obfuscation using graph-induced
    encoding* (ePrint 2017/104).
  * Wee, *ℓ-succinct LWE*, as `Def_SuccinctLWE` and its sources.
  * The texts already used by #84, #86 and #90: TLWE (ePrint 2026/2927), decomposed LWE (ePrint
    2026/2443), CVW18.
* **From secondary sources, with the original cited:**
  * Albrecht's "SIS with hints zoo" (malb.io/sis-with-hints.html) for k-SIS, OM-ISIS, k-R-ISIS,
    twin-k-R-ISIS, PRISIS, h-PRISIS and ISIS_f;
  * D. Wu, *Exotic lattice assumptions and how to tame them* (talk, 2025), for the evasive-LWE
    landscape.

  The exact distributions were checked only where they matter for the verdict.
* **Searched for, not found as falsifiable statements:**
  * a non-evasive "pseudorandom preimage" assumption from 2025–2026;
  * an assumption named "power-ℓ" or "intersection" (the closest are PRISIS and h-PRISIS).

  The ePrint web site could not be fetched from this session (bot check, and no browser was
  available), so a 2025–2026 ePrint paper that is not mirrored elsewhere may have been missed.

## 2. The row-space barrier (Lean kernel and informal closure)

**Lemma A (`Hints.zero_row_hint_exposes`, Lean).** Let `X` be a hint with `H X = Y`, and let `c`
be a row combination with `c Y = f`. Then

`(σ (cH) + e) X = σ f + e X`.

If `f` is small, the hint decodes every LWE-type sample along the row `δ = cH`.

**Lemma B (`Hints.rank_condition_necessary`, Lean, scalar case of WWW22 Assumption 4.1).** Suppose
a preimage oracle answers a query `M` whose row space contains the challenge direction `u`
(`u = cM`), with target `t`. Then the answer `y` gives

`⟨σ uB + e, y⟩ = σ⟨c, t⟩ + ⟨e, y⟩`.

With `⟨c, t⟩ = 0` this decodes the challenge. So the "`[u; M]` of full rank" condition of
related-trapdoor LWE cannot be dropped.

**Consequence for `ML_i`.**

* The children `D_{i+1,b}` are preimages under `A_i ∋ δ` with `δ`-targets `f_b` small.
* So if the challenge of an assumption were "an LWE sample along `δ`", Lemma A would break it.
  This is the cleanest form of #84's statement that a two-zero-child row cannot carry an LWE
  challenge.
* The leak `v_t` therefore needs the pad `ℓ^{lt}_i + c_t A^{con}_i`. Its targets at level `i+1`
  are not small, and they must stay pseudorandom given everything the adversary has downstream.
* Downstream there are witness completions, and the pad rows of the witness prefixes have honest
  zeros along them (canonical decryption, required because the hop is statement-independent).
* Any hint that the assumption supplies at level `i+1` therefore has the same structure: a
  preimage under a matrix whose rows reach zero targets along some suffix.

Iterating this down to the last level forces the instance of the assumption to contain a GGH15
encoding whose honest zeros lie below a planted row, i.e. the multi-pass program itself.
`GGH15.path_identity` gives the exact form of these zeros. This is the informal **closure
barrier**: under (N1)–(N2), the weakest hinted statement that implies `ML_i` is TSR_Ψ of #84.
That statement is already the open node `Reroute.multipass_subtree_hop`.

**What the LWE-provable hint assumptions do instead.** They all respect Lemma A by construction,
in one of four ways:

* the hints are preimages under matrices that **avoid** the challenge direction (related-trapdoor
  LWE, the `i ≠ i*` blocks of BASIS_rand);
* they carry a **shift** that has to be paid for on the challenge matrix (ℓ-succinct, shifted
  multi-preimage);
* they **declare** the decoded directions and take the challenge distribution only modulo them
  (k-LWE: uniform on `Span(x_i^+)^⊥`);
* the problem is a **search** problem (SIS-type), so no decision statement is supplied.

None of these four forms can express "zero-target preimages on a *hidden* row plus a masked leak
of that row".

## 3. Assumptions checked

| Assumption (source) | Type, falsifiable, statement-independent | Hint (h1, h2) | Decodes the challenge direction? (h3) | Gives the `ML_i` simulation? |
| --- | --- | --- | --- | --- |
| BASIS_rand (WW23 Asm. 3.3; SIS-hard by Thm 3.4) | search; yes; yes | gadget trapdoor of `B_ℓ = [diag(A_1..A_ℓ) \| −1_ℓ ⊗ G_{n+1}]`, `A_{i*} = [aᵀ; A]`, other `A_i` uniform | full decoding of every block `i ≠ i*`; block `i*` only up to the `G`-shift | **no**: a search problem, no zero targets; the `G`-shift is #90's slot shift |
| BASIS_struct (WW23 Asm. 3.3 eq. (3.1); §6.1: equivalent to "SIS hard given `A^{-1}(W_i^{-1} R)`") | search; yes; yes | preimages under the public `A` of `W_i^{-1} R` | single hints have **no zero row** (`Hints.basis_struct_no_zero_row`); short combinations with a chosen zero row `c` exist (one-row SIS), but that row `cA` is public, and Lemma A then decodes it | **no**. WW23 §6.1 justify the LWE analogue only through evasive LWE, and Remark 6.2 gives no reduction |
| PRISIS / h-PRISIS (Fenzi–Nguyen ePrint 2023/846; AFLN ePrint 2023/1469) | search; yes; yes | BASIS_struct with `W_i = w^i` (the "power" family) | as BASIS_struct | **no** |
| ℓ-succinct LWE / SIS (Wee 2024; `Def_SuccinctLWE`) | decision / search; yes; yes | trapdoor of `[I_ℓ ⊗ B \| W]` | decodes stacked samples (#90, `stacked_hint_decodes`) | **no**: shift-or-decode dichotomy (#90 §2) |
| Shifted multi-preimage trapdoor (WWW, EUROCRYPT 2025; from LWE) | decision; yes; yes | publicly derivable gadget trapdoor of `D_ℓ = [diag(A_k) \| 1_ℓ ⊗ G]`, with `A_k = B − u_k ⊗ G`: preimages `A_k π_k = t_k + c` with a common random shift `c` | not on a single `A_k` (somewhere hardness), stacked yes | **no**: this is succinct-shaped with `W = 1 ⊗ G`. Canonical decryption forces the shift to vanish on a spanning set of witness rows (#90, `eq_zero_of_spanning_annihilated`), and that gives back the decoding case |
| Generalized related-trapdoor LWE (WWW TCC 2022 Asm. 4.1; from LWE by Thm 4.2; BV22) | decision; yes; yes | oracle `((M ⊗ I_n)B)^{-1}(t)` for every `M` with `[u; M]` of full rank | never, and the rank condition is necessary (Lemma B) | **no**: `ML_i` needs exactly the excluded queries |
| k-LWE / k-SIS (LPSS14 Def. 15, Thm 18; BF11) | decision / search; yes; yes | `k ≤ m` short `x_i^+ = (1‖x_i)` in `Λ^⊥((uᵀ; A))`, i.e. preimages of `−u` under a public `A` | yes along `Span(x_i^+)`, and the definition compares to `U(Span(x_i^+)^⊥)` | **no**: the hints are under a public matrix, all have one target, and there are fewer than `m` of them. `ML_i` needs two rank-`m` families under a hidden matrix, and k-LWE with `k ≥ m` is vacuous |
| k-R-ISIS, k-M-ISIS, twin-k-M-ISIS (ACLMT22; BCFL23) | search; yes; yes | `u_g` with `A u_g = g(v)·t` | yes on the submodule spanned by `t`: Wee–Wu (ASIACRYPT 2023) build a short basis of `[A \| DG]` from the hints, which breaks the knowledge variant | **no**: no zero rows (`g(v)` is a unit) and no decision form |
| OM-ISIS, ISIS_f (AKSY22; BLNS ePrint 2023/560) | search with oracles; yes; yes | preimages of oracle-chosen or `f(x)` targets | yes for `≥ m` zero preimages (OM-ISIS lattice attack) | **no** |
| TLWE (AJLW, ePrint 2026/2927) | decision; yes; yes | a full trapdoor `T` of `A` with wide errors | in every regime compatible with WE correctness (#84, `decryption_recovers_noise`) | **no** |
| Decomposed LWE (`Def_DecomposedLWE`), tensor LWE | decision; yes; yes | none (product samples) | — | **no**: no preimages, no zero samples (#84 §3) |
| (Matrix) NTRU, decisional NTRU | decision; yes; yes | `h = g f^{-1}`: a hidden *short* row `f` with a short image | — | **no**. The one-node core of `ML_i` is NTRU-shaped (#84 §2.1 aside: a planted `(m+1)`-th short vector of the lattice of `[D_0 \| D_1]`). But NTRU hides a short secret, not a uniform `δ` with a masked leak, and it supplies no continuation. GGH13-style NTRU encodings are broken by zeroizing attacks |
| Evasive LWE (public- and private-coin), Root iO (ePrint 2025/2139), Diamond iO (ePrint 2025/236), Tsa22 / VWW22 WE, BDJMMPV24 | excluded (evasive; private-coin variants are counter-exampled, HJL and BÜW24) | preimages `A^{-1}(P)` of arbitrary structured `P` | — | excluded |
| HHSS17 "GGH15 with tags" (ePrint 2017/104) | not an assumption (an implementation; "tags" are the edges of the GGH15 DAG) | — | — | — |

**The pattern.**

* Falsifiable hinted assumptions with a decision form are LWE-provable (k-LWE, related-trapdoor
  LWE, shifted preimages, ℓ-succinct LWE with `ℓ = 1` or a wide `W`), or are justified only by
  evasive LWE (the LWE analogue of BASIS_struct, WW23 §6.1).
* The LWE-provable ones enforce Lemma A or Lemma B by construction.
* The others are search (SIS-type) assumptions. These cannot give the decision statement
  `ML_i`, unless they are combined with a decision assumption on the same hidden row, and then
  Lemma A applies again.

## 4. Instantiation attempt and cost

**Closest design.** Make the pass-1 chain levels of MP2 "shifted" levels:

* `A_{i+1,k} = B − u_k ⊗ G`, using the WWW25 public trapdoor;
* the children `D_{i+1,b}` are preimages under different `A_{i+1,k}`;
* the common shift `c` plays the role of the hidden row.

It fails in two ways:

* The chain `A_0 D_1 D_2 …` carries the shift as a term `C·D_{>i+1}`, which is not small
  (`GGH15.path_identity` with an extra non-short `E`). Canonical decryption on true statements
  forces it to vanish on a spanning set of witness rows.
* Making it vanish turns the public `D_ℓ`-trapdoor into a stacked decoder of the level (#90).
  This violates (N1).

No surveyed assumption passes (N1)–(N3), so no level of MP2 can be made to need exactly the
hints of one of them.

**Cost (unchanged).**

| | |
| --- | --- |
| MP2 dimensions (`pq-we-multipass-ggh15` §4) | `d ≈ 2^{23.6}`, `m ≈ 2^{40}`, `log q ≈ 2^{16.5}`, `L = 4352` |
| ciphertext and work | `≈ 2^{97}` bits |
| hops (`pq-we-hybrid-count-barrier`) | `≈ 2^{136}`, so premises of about 400 bits |
| status | conditional on `ML_i` for all `2(n − j)` merges per threshold |
| unconditional alternatives | XWE `≈ 2^{147.7}` (#83, open); brute force `≈ 2^{188}` |

## 5. Remaining gap

* **`ML_i` / `AdvancedEncryption.WE.Reroute.multipass_subtree_hop`** is still the only missing
  lemma of an efficient MP WE.
* **What a supplying assumption would have to state.** By §2, it must give preimages under a
  matrix that contains the challenge row, with targets that are small on that row. It must also
  hide that row through a pad whose targets stay undecodable through a continuation with honest
  zeros.
* **Where such statements exist.** In the literature only evasive-type statements say this, and
  they are excluded. A falsifiable statement of this kind is TSR_Ψ (#84). It is
  statement-independent, because the adversary chooses `Ψ`, but it is not from the literature.
* **What would help.** A literature assumption of the k-LWE form ("LWE is pseudorandom modulo
  the directions the hints decode") in which the hinted matrix is **hidden** (GGH15-style) and the
  hints are **square** would be the right shape. We found none. Wee–Wu's §6.1 question (is LWE
  hard given `A^{-1}(W_i^{-1} R)`?) is the nearest open question in the literature, and its
  targets have no zero rows.
* **Not done here.** Registering a new assumption. The rules require literature assumptions,
  and none fits.

## 6. Formal results (complete proofs)

* `AdvancedEncryption.WE.Hints.zero_row_hint_exposes`: `c (H X) = f ⇒ (σ (cH) + e) X = σ f + e X`
  over any commutative ring (Lemma A).
* `AdvancedEncryption.WE.Hints.rank_condition_necessary`: `u = cM`, `(MB) y = t ⇒
  ⟨σ uB + e, y⟩ = σ⟨c, t⟩ + ⟨e, y⟩` (Lemma B; the rank condition of related-trapdoor LWE is
  necessary).
* `AdvancedEncryption.WE.Hints.basis_struct_no_zero_row`: over a field, with `W` invertible and
  `R` right-invertible, `c (W^{-1} R) = 0 ⇒ c = 0` (BASIS_struct targets have no zero row).

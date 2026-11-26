---
title: Direct WE designs with native per-hop LWE steps - wire-indexed systems, tensor and Gray walks, public-trapdoor extraction, GSW products; native kills exist, re-encoding is the gap
refs: [definition:WE_CircuitSAT, definition:GGH15, definition:WE_MaskedGGH15, definition:SuccinctLWE, definition:DecomposedLWE, note:pq-we-summary-2026-11, note:pq-we-hybrid-count-barrier, note:pq-we-function-hiding-crux, note:pq-we-evaluation-oracle-crux, note:pq-we-affine-syzygy-barrier, note:pq-we-linear-hop-barrier, note:pq-we-matrix-collision-barrier, note:pq-we-new-directions, note:pq-we-tree-candidate-crux, note:pq-we-witness-prf-masked-evaluator, note:pq-we-multipass-ggh15, note:pq-we-mp2-cryptanalysis, note:pq-we-two-pass-reroute, note:pq-we-two-sided-lwe, note:we-circuitsat-bruteforce-explicit-cost, theorem:AdvancedEncryption.WE.CertDual.dichotomy, theorem:AdvancedEncryption.WE.Wee.leaf_trapdoor, theorem:AdvancedEncryption.WE.Hybrid.stat_hops_carry, theorem:AdvancedEncryption.WE.MaskedGGH15.masked_decrypt, theorem:AdvancedEncryption.WE.NativeHop.nand_reach_saturate, theorem:AdvancedEncryption.WE.NativeHop.gsw_path_product, theorem:AdvancedEncryption.WE.NativeHop.kron_noise_cross, theorem:AdvancedEncryption.WE.NativeHop.lex_prefix_cubes, theorem:AdvancedEncryption.WE.NativeHop.zero_entry_hint]
tags: [witness-encryption, strategy, barrier, candidate, open-problem]
---
Design-AI sub-task (kk) on `Def_WE_CircuitSAT` (NAND Circuit-SAT, 128-bit witnesses, `2^12`
gates, `λ = κ = 128`). The request was to leave the XWE / ABE-enumeration routes, look for a
**direct** WE with ciphertexts polynomial in the statement (target `≤ 2^60` bits), and in
particular for a design whose per-hop step is a plain LWE (or LPN) instance **by construction**.
Allowed: falsifiable, statement-independent post-quantum assumptions. Forbidden: iO/xiO, evasive
LWE, local mixing, statement-dependent assumptions.

The five `NativeHop.*` theorems have complete Lean proofs (Mathlib only). Everything else is an
informal argument, checked step by step by the submitting agent. Open PRs of the DAG are cited by
number only.

## 0. Answer

* **No direct design with native hops and a complete proof was found.** Four directions were
  worked out (a–d), plus one that came up on the way (e). Each ends at one of three obstacles:
  * **O1, mix-and-match saturation.** Any scheme whose wire labels depend only on `(wire, value)`
    gives the label of output value `1` on every statement (`nand_reach_saturate`).
  * **O2, linear closure / structural collision.** A scheme whose decryption is a fixed short
    combination of noisy samples, or whose evaluated matrices are the same for all candidates,
    leaks through short combinations that the attacker can also form. This is the barrier of
    `pq-we-evaluation-oracle-crux` and `pq-we-matrix-collision-barrier`, and the
    statement-dependent lattice of `CertDual.dichotomy`.
  * **O3, re-encoding across departures.** Product (GGH15 / GSW) designs avoid O1 and O2. Their
    walks need a functionality-preserving *re-encoding* of the erased set at almost every hop
    (§6, a counting argument). Leaf-first LWE cannot carry such a re-encoding past a level with a
    zero program entry (`zero_entry_hint`).
* **Native kills exist when the candidate is isolated.** The step "kill candidate `k` using
  `φ(k) = 0`" has three local forms (§1): the `−G` leaf trapdoor (`Wee.leaf_trapdoor`, Lean), a
  restricted polynomial refutation (`CertDual.dichotomy`, Lean), and the erasure of a subtree
  with a falsified clause once that subtree is its own class (ERASE of `pq-we-multipass-ggh15`,
  argued informally there). The kill is therefore not the core difficulty. The core difficulty is
  keeping a poly-size representation of the hybrid while the erased set grows, in which the next
  candidate is isolated.
* **Best direct design: additive-pad GGH15 (APG, §6).** It is a masked γ⊗-GGH15 Tseitin
  encoding (the single-pass candidate of `pq-we-witness-prf-masked-evaluator`) with `n = 128`
  extra pad slots. Hybrid `H_k` pads the `≤ n` subcubes of `{w < k}` (`lex_prefix_cubes`).
  The walk has no comparator, so there is no reroute in the MP2 sense. Each hop is one
  witness-local **point insertion (PI)** and, amortized, one statement-independent,
  functionality-preserving **pad merge (PM)**.
* **Precise gap.** Neither PI nor PM is proved. PM is statement-independent and changes values
  only on a fully padded cube, so it is outside the live-class consistency barrier of
  `pq-we-two-pass-reroute` §4. But a cube program has zero entries at the departures from its
  prefix, and the live witnesses that depart there see the slot's rows in their noise. This is the
  hidden-row structure of `ML_i` again. PI is ERASE without a class split. Both reduce to one
  missing tool: **an LWE argument that crosses a zero program entry**
  (`zero_entry_hint` shows why the CVW18 leaf-first move cannot).
* **Cost.** APG costs about `2^{97}` bits (the single-pass masked GGH15 cost plus `< 1%`),
  polynomial and far below brute force (`2^{188}`, `we-circuitsat-bruteforce-explicit-cost`),
  but **not `≤ 2^60`**. Every GGH15 Tseitin encoding pays `2L·m²·log q` with `L ≥ 4224` levels.
  The designs that would meet `2^60` (BGG+-shaped, about `2^{37}` bits) are exactly the ones that
  O2 kills.

## 1. What "native" means, and the local identities that `φ(k) = 0` can supply

By `pq-we-hybrid-count-barrier` (and `Hybrid.stat_hops_carry`), every statement-independent proof
has some hops that are valid only on false instances. A native hop at candidate `k` therefore has
the shape

`H_k  ≈_LWE  Sim_k(real)  ≡_local  Sim_k(uniform)  ≈_LWE  H_{k+1}`

* The two LWE moves are valid for every `φ`.
* The middle move is an exact or statistical identity that holds *because `φ(k) = 0`*, computed
  from `φ` and `k` alone.

Three local identities are known (I1 and I2 with Lean proofs, I3 with an informal LWE proof):

| | Identity created by `φ(k) = 0` | Where proved |
| --- | --- | --- |
| I1 | planted candidate: with `A_wit = B R + k ⊗ G`, BGG+ evaluation gives `A_φ = B R_φ`, a `−G` trapdoor for `[B │ A_φ − G]` | `Wee.leaf_trapdoor` (succinct LWE, `Def_SuccinctLWE`) |
| I2 | restricted refutation: the restricted indicator `χ_k` lies in the Nullstellensatz span, so the hop is perfect | `CertDual.dichotomy` (`pq-we-new-directions` §2.4) |
| I3 | falsified clause on a subtree: the subtree of node `k` is erased by leaf-first LWE on a (class, clause) block | ERASE, `pq-we-multipass-ggh15` §4 |

A fourth form, "absence of a zero" (`M_k ≠ 0` in a diagonal branching program), is not an
identity. It is the masked-leak step `ML_i` of `pq-we-two-pass-reroute` and is not proved.

## 2. Direction (a): the ciphertext as a noisy linear system indexed by wires

**(a1) Value-labelled wires (garbled-circuit shape, with or without rounding).** For each wire `j`
and value `v` there is a label `L_{j,v}` (an LWE secret, a sample `s_{j,v}ᵀA + e`, or an LWR value
`⌊s_{j,v}ᵀA⌉_p`). Per gate and per input pair `(α, β)`, public data lets the evaluator map
`(L_{a,α}, L_{b,β})` to `L_{c, NAND(α,β)}`: linear relations, LWE re-encryption keys, or
rounded products. The output label `L_{out,1}` unlocks `μ`. The encryptor does not know the
witness, so the labels of both values of every input are derivable.

* **Correctness:** follow `w`.
* **Hop structure:** each gate step is a single LWE re-encryption, so it looks native.
* **Attack (complete, every statement):** let `R(j)` be the set of values whose label for wire
  `j` the evaluator can derive. Then `R` is `{0,1}` on inputs and closed under propagation, so
  by `nand_reach_saturate` it is `{0,1}` on every wire, including `out`. Rounding, modulus
  switching and LWR change how a label is computed, not *which* labels are computable, so they do
  not help. This is the classical mix-and-match attack, here for every statement at once.

**(a2) Path-dependent labels.** Escaping O1 requires the label of a wire to depend on the whole
assignment, not on `(wire, value)`. Then the final label `L_out(w)` takes `2^{128}` values, and the
encryptor needs a path-independent read-out that works only on consistent paths. The only known
mechanisms are read-once products (GGH15 / branching programs: every level string is an
assignment) and equality clauses between copies (`pq-we-multipass-ggh15`). Both are direction (b).

**(a3) Polynomial systems.** The wires become variables, decryption is a linear functional on the
monomial vector, and this is exactly the certificate-dual scheme of `pq-we-new-directions` §2:
statistically secure on certified-false statements, with security elsewhere equal to "no short
pseudo-solution" (statement-dependent, O2). At degree 2 with one variable per wire, a short
pseudo-solution exists for every circuit whose gates read two distinct wires and whose output
wire feeds no gate: set `L(1) = L(x_j) =
L(x_j x_out) = 1` and `L(x_a x_b) = 0` for the input pairs of the gates. Then
`L(x_c + x_a x_b − 1) = 0` for every gate and `L(m(x_out − 1)) = 0` for every `m` of degree at
most 1, so `L` decrypts.

**Where non-linearity enters.** The affine-syzygy barrier (escape 2) leaves rounding and `G^{-1}`
as non-linear processing. (a1) shows that applying them per wire does nothing against O1: the
non-linearity has to sit on the *path* (products), which is (b) and (d).

## 3. Direction (b): Gray-code walks and tensor / Kronecker LWE

**(b1) Tensor samples with witness-selected factors.** The ciphertext holds
`y_{i,b} = s_{i,b}ᵀA_{i,b} + e_{i,b}`, and decryption tensors `y_{1,w_1} ⊗ ⋯ ⊗ y_{n,w_n}` against a
public functional.

* **Failure:** by `kron_noise_cross`, `(Y₁+E₁)⊗(Y₂+E₂) − Y₁⊗Y₂` contains `E₁⊗Y₂` and `Y₁⊗E₂`, which
  are small noise times uniform values, hence not small. Noisy tensor decryption needs every
  factor but one to be *short*: Gaussian preimages (GGH15) or `G^{-1}` of public matrices
  (GSW / BGG+ / BP14).
* **Decomposed LWE** (`Def_DecomposedLWE`) is the 2-factor case with short `B_j`. Its access
  structure is closed under short linear combinations (`pq-we-matrix-collision-barrier`,
  rank-one variant), which is O2.

**(b2) Hops on factors.** In any product encoding, the datum `(level i, bit b)` is read by all
`2^{n−1}` candidates with `w_i = b`. A hop that changes one factor therefore has to preserve
the values of the `2^{n−1} − 1` other candidates in that half-cube. So it is a
functionality-preserving re-encoding, not a kill. Gray order makes consecutive candidates differ
in one bit, but the *set* of erased candidates still changes its cube structure by carries
(amortized `O(1)` per hop in both orders), so Gray order does not remove the re-encoding (§6).

**(b3) Hops on subcubes.** ERASE (I3) kills a whole subtree in one provable hop. But a false
`Tseitin(φ)` whose subtrees each falsify a clause needs about `2^{128}` subtrees (one per input
assignment, along its gate path), and all of them must be kept as separate classes unless they
are merged. This is §6 again.

## 4. Direction (c): public trapdoor only for the final extraction

The ciphertext is `CT = sᵀM + e` with a statement-dependent public `M`, together with a public
matrix `B` that has a *public* trapdoor `T_B`. A witness gives a short `H_w` with `M H_w = B`.
The decryptor computes `CT·H_w = sᵀB + small`, decodes `s` with `T_B`, and reads `μ` from a further
sample `sᵀu + μ⌊q/2⌋`.

* **Reduction:** this is linear decryption with a matrix-valued target. `CertDual.dichotomy`
  applies column by column. If `B ∈ range(M)` with short preimages, decryption works. If not,
  security is "no short `H` with `M H = B R` for short `R`", which is a property of the lattice of
  `M`, that is, statement-dependent.
* **"No short vector unless witness" plus LWE** is a GapCVP-type promise for the specific
  lattice of `φ`. By `pq-we-hybrid-count-barrier` its statistical part only covers promise
  problems in SZK. The computational part needs LWE with the structured matrix `M`, which no
  statement-independent assumption provides.
* **Walk:** I2 hops (restricted refutations) are native, but at a non-refutable restriction the
  hop again needs the statement-dependent lattice property (`pq-we-new-directions` §2.4).

Verdict: O2.

## 5. Direction (d): circular GSW, witness bits choosing the gadget decompositions

The ciphertext holds GSW matrices `C_{i,b} = A R_{i,b} + x_{i,b} G` (or matrix plaintexts of a
branching program for `Tseitin(φ)`), possibly with circular encryptions of the GSW key. The
decryptor multiplies along `w`.

* **Correctness identity** (`gsw_path_product`): `C_{1,w_1} G^{-1}(C_{2,w_2} G^{-1}(⋯)) =
  A R_w + (∏ x_{i,w_i}) G`. The plaintext product is exactly the branching-program value, and
  consistent paths are all paths because the program is read-once.
* **Failure:** reading `∏x` from `A R_w + (∏x)G` needs a vector `t` with `tᵀA ≈ 0`, the GSW
  secret. Suppose every ciphertext component lies in the family covered by (circular) GSW
  security. That is a statement-independent assumption with a polynomial-hop proof, so it makes
  the ciphertext pseudorandom for true statements too, which contradicts correctness. Hence the
  extraction component must be outside GSW. It is then either a GGH15-type public zero test
  (back to (b)) or a compute-and-compare obfuscation (e).
* **"Consistent paths cancel"** (two programs whose products agree exactly on witnesses) is an
  evaluation collision in the sense of `pq-we-matrix-collision-barrier`. The `A R_w` parts of two
  products agree only if the decompositions are equal, which is structural (O2).

**(e) Compute-and-compare / lockable obfuscation (GKW17, WZ17).** `Obf(P, y, μ)` with
`P(w) = y` on witnesses. The LWE proofs need `y` to be unpredictable (or pseudo-entropic) given
`P`. Since `P` computes `y` from any witness, "`y` is pseudo-entropic given `P` on false `φ`" is
WE security of `P` itself, so (e) reduces WE to WE. If instead `P` contains a public-key FHE, the
attacker can encrypt the lock value directly.

## 6. Best design: additive-pad GGH15 (APG), its walk, and the exact gap

**Construction.** Start from the single-pass masked γ⊗-GGH15 WE of
`pq-we-witness-prf-masked-evaluator` §5 (`Def_WE_MaskedGGH15`):

* Levels read `w`, then the Tseitin gate values.
* Secrets `diag(R_i, M_{i,b} ⊗ S'_{i,b}, S_{i,b})`: mask block, CNF constraint block, CPRF block.
* Two left vectors `u_O`, `u_C`, whose rank-one difference cancels the CPRF block.
* Decryption value `V(z) = mask − C(z) + noise`, with `C(z) = 0` iff `z` satisfies `Tseitin(φ)`.

APG adds `n = 128` **pad slots**. Slot `c` is a γ⊗ block `M^{(c)} ⊗ S^{(c)}` with fresh
bit-dependent secrets, read only through `u_O`. Its program is the indicator of a subcube of the
witness space: width 1, at prefix level `i` the scalar `[b = p_i]`, then `1`. In the real scheme
every slot carries the zero program. Decryption is unchanged:
`V(z) = mask − C(z) + Σ_c pad_c(z)`.

**Correctness.** The pads are zero in the real scheme, so decryption is that of the base scheme
(`MaskedGGH15.masked_decrypt`).

**Walk** (lexicographic order, `k = 0 … 2^n`).

* By `lex_prefix_cubes`, `{w < k}` is the disjoint union of at most `n` subcubes, one for each
  `1`-bit of `k`. `H_k` has these cubes in its pad slots, so every `w < k` is padded.
* Hop `k → k+1` with `φ(k) = 0`:
  1. **PI (point insertion):** put the point cube `{k}` into a free slot. This is witness-local:
     it is valid only because `C(k) ≠ 0`.
  2. **PM (pad merges):** merge sibling cubes, as many times as `k` has trailing ones. Merging
     replaces the slots `Q_0 = p0∗` and `Q_1 = p1∗` by `p∗` and a zero slot.
     PM is statement-independent and preserves the distribution of every `V(z)`: both sides pad
     exactly `Q`, with independent pseudorandom pads.
* In total `2^n` insertions and `2^n − 1` merges, so about `2^{129}` hops plus the internal hops
  of each lemma. That needs premises of about `128 + 2·(129 + log(internal hops)) ≈ 400` bits.
  `H_{2^n}` pads every `z` with one full-cube block read only through `u_O`, and `mask` must be
  hidden there. This last step is a one-left-vector-type statement and is expected, not proved.

**Why re-encoding cannot be avoided (counting).** A pure-insertion walk (no merges) represents
`{w < k}` as a union of atoms that are never removed. A poly-size representation therefore covers
at most (number of slots) × (largest atom) candidates. Reaching all `2^{128}` candidates needs
either atoms killed in one hop, which needs subtree refutations (I3) and there are about
`2^{128}` of them for a generic false circuit, or merges. Every poly-size positional walk
therefore makes a functionality-preserving re-encoding in all but polynomially many hops: PM here,
the reroute in MP2, the internal node of `pq-we-tree-candidate-crux`.

**Attacks on APG (false statements).**

* Zeroizing (CVW18 §9 rank, CHL+15/CLLT16, statistical zeroizing): there is no small evaluation,
  because every `V(z)` carries the uniform `mask` and `C(z) ≠ 0`. The real scheme's zero pad slots
  only add noise inside sums that are never small.
* Rank tests restricted to a pad slot: the rectangles inside a cube `p∗` with the prefix fixed have
  two rows (the bit after `p`), far below `n'`.
* Subtraction / inclusion–exclusion: blocked by bit-dependent pad secrets, as for the constraint
  block (`pq-we-witness-prf-masked-evaluator` §5, attack 1).
* Mixed input: the encoding is read-once, so every level string is an assignment.
* Rank of the left vectors: the pad rows enter only the one exposed combination `u_O − u_C`, as
  the mask rows do. That keeps the rank-one condition of the base scheme.

**The exact gap.**

* **PM (pad-merge lemma).** In APG at any hybrid, replacing two sibling-cube pad slots by their
  parent cube and a zero slot is LWE-indistinguishable, for every CNF (statement-independent).
  * Not refuted.
  * Outside the live-class consistency barrier: values change only on the fully padded cube `Q`.
  * Not provable with the CVW18 leaf-first move. At a prefix level `i ≤ |p|`, the program entry
    for `b ≠ p_i` is `0`, so the slot rows of the preimage satisfy `A^{(c)}_{i−1} D_{i,b} = E`.
    By `zero_entry_hint`, every LWE sample `S A^{(c)}_{i−1} + E'` then satisfies
    `(S A^{(c)}_{i−1} + E')D_{i,b} = S E + E' D_{i,b}`, which is short. So the rows of level
    `i − 1` are not a fresh LWE secret. Live witnesses that depart from `p` at level `i` see these
    rows in their noise. This is the hidden-row structure of `ML_i` (`pq-we-two-pass-reroute`
    §7, `pq-we-two-sided-lwe`), now without a live class on the changed side.
* **PI (point-insertion lemma).** For `φ(k) = 0`, inserting the point program `{k}` into a zero
  slot is LWE-indistinguishable. It is ERASE (I3) without a class split. Its natural proof runs
  through the falsified clause of `k`'s gate path, whose block is shared with every other path
  falsifying that clause. Not proved.
* **Common missing tool:** an LWE argument that crosses a zero program entry of a GGH15 level
  while the departing strings stay live. With it, PM and PI would follow by the CVW18 leaf-first
  method, and APG would be a complete WE at about `2^{97}` bits from LWE at about 400-bit
  strength.

## 7. Cost summary

| Design | Ciphertext (bits) | Status |
| --- | --- | --- |
| (a1) value-labelled wires, LWE/LWR gates | `≈ 2^{12} · 4 · m log q ≈ 2^{36}` | broken on every statement (O1) |
| (a3)/(c) polynomial or trapdoor-extraction linear systems | `N_D log q` (`2^{33.5}` at `D = 3`) | statement-dependent (O2); `D = 2` broken |
| (b1) tensor samples, decomposed LWE | `≈ 2^{30}–2^{40}` | O2 / noise blow-up (`kron_noise_cross`) |
| (d) GSW products | `≈ 2L · m² log q` | needs a non-GSW extraction component; that component becomes (b) or (e) |
| (e) compute-and-compare | — | circular (WE ⇒ WE) |
| **APG** | **`≈ 2^{97}`** (single-pass masked GGH15, `L ≈ 4224`, `m ≈ 2^{40}`, plus `128` slots of width `n'`) | open: PM and PI |

The `2^{60}` target fails for every GGH15-type design. `log q ≥ L·log₂√m` with `L ≥ 4224`
levels forces `m ≳ 2^{38}`. Fewer levels need a branching program for the circuit itself, whose
width grows exponentially with depth for general circuits.

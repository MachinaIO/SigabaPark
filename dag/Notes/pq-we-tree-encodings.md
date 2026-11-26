---
title: Tree encodings (Abram-Malavolta-Roy, ePrint 2026/741) for post-quantum WE - what they give, three constructions, why section 4.4's proof fails, and the evaluation crux in read-once form
refs: [definition:WE_CircuitSAT, definition:DecomposedLWE, definition:SuccinctLWE, note:pq-we-evaluation-oracle-crux, note:pq-we-hybrid-count-barrier, note:pq-we-affine-syzygy-barrier, note:pq-we-function-hiding-crux, note:pq-we-matrix-collision-barrier, note:pq-we-tree-candidate-crux, theorem:AdvancedEncryption.WE.Tree.sum_paths_prod, theorem:AdvancedEncryption.WE.Tree.path_expansion, theorem:AdvancedEncryption.WE.Tree.key_mul, theorem:AdvancedEncryption.WE.Tree.universal_key, theorem:AdvancedEncryption.WE.Tree.root_encoding_leak, theorem:AdvancedEncryption.WE.Tree.fixed_offset_attack]
tags: [witness-encryption, candidate, attack, barrier, open-problem]
---
Design-AI sub-task on `Def_WE_CircuitSAT`. The question was whether the **tree encodings** of
Abram, Malavolta and Roy, *Tree Encodings I: How to Authenticate a Truth Table* (ePrint 2026/741,
"AMR26" below), allow key-homomorphic evaluation over all `2^128` witnesses, and so serve as
(a) a public evaluator for the master function of `pq-we-evaluation-oracle-crux` with a
tree-structured hybrid, (b) the split lemma of the positional GGH15 candidate (open PR #42), or
(c) a direct WE. Short answer: **no, for structural reasons that can be stated precisely**. Tree
encodings make the *constrained-key* side of the crux universal and laconic. They leave the
*master* side unchanged, and their laconic ciphertexts fall inside the affine-syzygy barrier.
Six algebraic facts used below are theorem nodes with complete proofs
(`AdvancedEncryption.WE.Tree.*`). The rest is informal.

## 1. What tree encodings give, precisely

Parameters `q = 2^K`, `n = k log q`, `t = 2mn`; public `pk = (A, B, P)` with `A ← Z_q^{tk×m}`,
`B ← D_σ^{m×tn}`, `P = [P_0 | P_1]` a fixed short matrix, and
`Z = [Z_0 … Z_{t−1}]`, the `k`-row blocks of `AB − I_t ⊗ G`. Under decomposed LWE
(`Def_DecomposedLWE`; AMR26 Definition 1), `z = sᵀZ + e` is pseudorandom, also jointly with LWE
samples of `s` on any further random matrices.
(Caveat: `Def_DecomposedLWE` claims strength only for prime `q`, Theorem 4.2's regime, while
AMR26 needs `q` a power of two for gadget decoding and rounding. A tree-encoding submission would
need the power-of-two regime registered.)

* **Truth-table hashing (Lemma 6).** For a read-once matrix branching program
  `BP(α) = ∏_i M_{i,α_i}`, the Merkle root `Σ_α (∏_i D_{α_i}) e_0 BP(α)` over all `2^d` inputs
  equals `∏_i (D_0 ⊗ M_{i,0} + D_1 ⊗ M_{i,1}) e_0`, so it costs `poly(d, dim BP)`. The algebraic
  core is `AdvancedEncryption.WE.Tree.sum_paths_prod` (ordered products distribute over all
  paths, in any semiring).
* **Path expansion (Lemma 7).** One step `(h_ρᵀ ⊗ G) P_b − Z Q_{y_ρ,b} = h_{ρb}ᵀ ⊗ G` composes
  along a path: `AdvancedEncryption.WE.Tree.path_expansion`.
* **Key equation (Theorem 5).** For every `f : {0,1}^d → Z_q` of depth `δ` there are a public
  binary `M_f` (from `f` only), a public `P_α` (from `α` only) and a public `H_{f,α}` of norm
  about `(tmn⁴)^{dδ}` with `G(M_f P_α − f(α) I_n) = Z H_{f,α}`. The invariant is kept by
  addition, constants, multiplication (`AdvancedEncryption.WE.Tree.key_mul`, Lemma 10) and
  flattening, which re-hashes the truth table of each entry of the current branching program.
  `TreeExpand` has depth `O(log d · log(mn log q))`: this **laconicity** is the paper's point.

**Reading for WE.** `AdvancedEncryption.WE.Tree.universal_key`:
`z H_{f,α} = sᵀ G M_f P_α − f(α)·sᵀG + e H_{f,α}`. So the single sample `z`, independent of the
statement and of the input, is a **universal constrained key**: a BGG+ encoding of *all*
inputs at once. Compare BGG+, where `c_1 = sᵀ(A − φ ⊗ G) + e` gives
`c_1 H = sᵀ A_{U_w} − φ(w)·sᵀG + noise`. The roles are:

| | BGG+ (oracle crux) | tree encoding |
| --- | --- | --- |
| constrained key | `c_1`, depends on `φ` | `z`, depends on nothing |
| master value at `w` | `sᵀ A_{U_w}` | `sᵀ G M_φ P_w` |
| offset | `φ(w)·sᵀG` | `φ(w)·sᵀG` |

On a false `φ`, `z` computes the master everywhere, exactly as `c_1` does. So the WE crux is
again: a representation of the master `w ↦ ⌊sᵀ G M_φ P_w⌉_p` that can be swapped for one built
from `z`.

## 2. The master side: three forms, none representable

**(i) Normal form.** `M_f = G^{-1}(G[h_{rs}ᵀ ⊗ I_n]_{rs})`, so `G M_f = [h_{rs}ᵀ ⊗ G]` with the
public Merkle roots `h_{rs}`, and `sᵀ G M_f P_α = f(α)·sᵀG + sᵀ Z H_{f,α}`. **The master equals
the WE output plus a term computable from `z`.** Representing it is the same as representing
`w ↦ φ(w)·sᵀG`, i.e. WE itself. Theorem 5's normal form only restates the problem.
*Construction T1* publishes the root `c = sᵀ G M_φ + e`. `root_encoding_leak`: its blocks are
`sᵀ(h_j G) + e_j`, and for any odd (unit) `h_j`, multiplying by the binary
`G^{-1}(h_j^{-1} G)` gives `sᵀG` plus short noise. Gadget decoding returns `s`. **Dead**,
for every `φ`.

**(ii) BGG+ master via LFE (the shift-hiding PRF of AMR26 §4.2).** With
`g(α) = vec(LFE.Hash(crs, f_α)) = vec(G^{-1}(Ā_{f_α}))`, `Eval(K, α) = ⌊sᵀ G M̃ P_α V'⌉_p`
equals `⌊sᵀ Ā_{f_α} + sᵀ Z H V'⌉_p`: the master of `pq-we-evaluation-oracle-crux` (BV15's
`sᵀA_f`) plus a `z`-term. Tree encodings make it **laconic** (depth polylog, independent of the
size of `f`). They do not change it.

**(iii) Hidden random root (Lemma 5 with arbitrary `M`).** Lemma 5 holds for every `M`:
`G(M − h_ρᵀ ⊗ I)P + Z Q = G(M P_b − h_{ρb}ᵀ ⊗ I)`. With `M` uniform and **secret**,
`c = sᵀ G(M − h_φᵀ ⊗ I) + e` is pseudorandom (decomposed LWE with auxiliary matrix `GM`). It is a
compressed BGG+ encoding whose attribute is the whole (tree-encoded) truth table of `φ`. Its
master is
`F_v(w) = ⌊v P_w⌉_p`, `v = sᵀ G M` uniform, `P_w = ∏_i (I ⊗ P_{w_i}) R`,
a **rounded linear functional of a public read-once branching program with fixed short
transitions**. This is the cleanest statement-independent form of the crux found so far.
Representations tried:
1. `v + e` (noisy key): `v − c = sᵀ(h_φᵀ ⊗ G) + noise`, then `root_encoding_leak`. Dead.
2. Kilian randomization `S_{i−1}(I ⊗ P_b)S_i^{-1}` with exact arithmetic: the transitions are
   public and the same at every level, so `S_{i−1}, S_i` are found up to the commutant of
   `{P_0, P_1}` by solving linear equations. Even with hidden `S`, exact outputs give linear
   equations in the noises of `c` and `z` (on a false `φ`, the exact `v P_w` minus the value
   expanded from `(c, z)` is a known linear form in those noises), and these determine them,
   hence `s`. Rounding is needed, and rounding is not linear. Dead.
3. GGH15 encoding with the public `I ⊗ P_b` as level secrets: the `S`-matrices are known, so
   `A_{i−1} D_{i,b} − (I ⊗ P_b) A_i` is short. Combining the two bits gives short vectors near
   `ker A_{i−1}`, and the backward kernel propagation of `pq-we-affine-syzygy-barrier` (escape 1)
   applies. With tensor randomization `S = (I ⊗ P_b) ⊗ R_{i,b}` (CVW18) the encodings are
   pseudorandom from LWE, but the decryptor gets `(v ∏ P) ⊗ (r ∏ R) A_d`, a per-path junk factor
   that it cannot remove. Dead as a direct representation; it is the GGH15 route of PR #42.
4. A second tree encoding (other `pk'`, other `M'`) agreeing on all `w`: an evaluation
   collision (`pq-we-matrix-collision-barrier`). With shared matrices it is the `X = A` leak.

## 3. Construction T2: the universal (statement-independent) tree

Put the statement in the input: `y = (φ, w)`, `U(y) = φ(w)`, master `O(y) = ⌊sᵀ G M_U P_y⌉_p`.
`O` is statement-independent, which is what the hybrid-count barrier asks of the evaluator. But
`O(y) − ⌊z H_{U,y}⌉_p = U(y)·⌊sᵀG⌉ ± 1` for **every** `y`, so `O` together with `z` returns `sᵀG`
at any satisfying pair the adversary makes for itself. A universal `O` is only safe next to a key
that cannot evaluate at other statements: the witness-PRF masking of agent (l), section 5.

## 4. Construction T3/T4: shift-hiding PRF, and why section 4.4's proof fails

**T3.** Shift `K` by `β = (φ, μ)` with `f(w, β) = φ(w)·μ`. Then
`ShiftEval(K_β, w) = Eval(K, w) + φ(w)μ` (AMR26 Lemma 13), `K_β = (pk, crs, z, ec, t)` is
pseudorandom by one decomposed-LWE hop (Lemma 14), and decryption needs a public evaluator of
`Eval(K, ·)`, a statement-independent function. Same crux, in laconic form.

**T4 (two shifted keys of one master).** Publish `K_{(φ,μ)}` and `K_{(φ,0)}`: the difference
of their evaluations is `φ(w)μ`, with no evaluator for `Eval`. With one `crs`, the two LFE
encodings contain `b_i = sᵀ(Â_i − c_i Ḡ) + ê_i` and `b'_i = sᵀ(Â_i − c'_i Ḡ) + ê'_i`, and
`b_i − b'_i = (c'_i − c_i)·sᵀḠ + noise` decodes `s` at any position where the GSW bits differ
(which they do, since GSW encryption is randomized). With two `crs`, the two `Eval` functions are
different masters, and their agreement on all `w` is an evaluation collision. **Dead.** More
generally, 2-key shift hiding for shifts that agree as functions is 2-key private constrained
PRFs, which imply iO (Canetti–Chen, Eurocrypt 2017).

**Section 4.4 (heuristic iO) made precise.** The obfuscation of `C` is `K_{β_K}` with
`f(α, β_K) = C(α) − Eval(K, α)`, so `β_K` contains `K`, in particular `s`. Lemma 14's reduction
builds `ec` from a decomposed-LWE challenge in `s`. It must write the GSW ciphertexts
`C_i = [B̂_i; sᵀB̂_i + e_i] + β_i G` and the encodings `sᵀ(Â_i − c_i Ḡ)` with `Â_i = Â*_i + c_i Ḡ`.
For fixed `β` it can, since it knows `β`. For `β = β_K` the plaintext contains the challenge
secret: this is a KDM (circular) statement for GSW + BGG+ + `z` under one `s`. Two observations
settle what kind of circular assumption could help:

* **The naive KDM form is false.** "`(z, ec(C, K)) ≈ (z, ec(C, 0))`" for all public `C` would
  make `Obf(C) ≈ K_{(C,0)} ≈ U` by Lemma 14, for every `C`. But `Obf(C)` evaluates to `C`, so
  `Obf(0)` and `Obf(1)` are distinguishable. So the circular step is false for every `C`, not just
  unproved. This also rules out the allowed "circular LWE" family as a direct fix.
* **The only consistent form is iO-type.** What could be true is
  `Obf(C) ≈ Obf(C')` for `C ≡ C'` as functions. For WE (`C(w) = φ(w)μ`, or `PRF(w) + φ(w)μ` to
  make the outputs pseudorandom, compared with `C' = PRF`), the class "equivalent to `C'`" is
  `φ`-dependent and not efficiently checkable. Read as "pseudorandom obfuscation of every
  pseudorandom `C`", it is false in general (the impossibility result of [BDJ+25] cited by AMR26), and it is
  exactly the step that `pq-we-hybrid-count-barrier` forbids from being a single
  statement-independent hop.

AMR26's *provable* uses of circularity (the obfuscated preimage sampler, Theorem 8) work because
the real parameters contain keys shifted by `0`, and the proof plants shifts **in an order where
each key's shift input is independent of that key** (`K̃_2` by `(K̃, τ)`, then `K̃` by
`(K̃_1, K_2)`, then `K̃_1` by `(K, M_0, M_1)`). The functionality changes, but every output is used
only as randomness or masked by a hidden `Eval`. WE needs an output that the decryptor
**unmasks**, so this trick supplies randomness and never decryption.

## 5. Relay for the witness-PRF idea (agent (l))

`O(x, w) = CPRF(k, (x, w)) + PRF(k', x)` with a constrained key for `C(x, w) = 1`.
`AdvancedEncryption.WE.Tree.fixed_offset_attack`: if the constrained key evaluates
`CPRF − u` on rejecting pairs for **one fixed offset** `u`, which holds for BV15-type
key-homomorphic CPRFs and for the tree-encoding universal key (`u = sᵀG`), then any true
statement `x'` that the adversary builds, with one witness `w_1` and one non-witness `w_0`, gives
`u = (O − CK)(x', w_0) − (O − CK)(x', w_1)`, and then `PRF(k', x) = (O − CK)(x, w) − u` for
**every false** `x`. With rounding the attack holds up to `±1`, which still breaks
pseudorandomness. So (l) needs a constrained key whose off-constraint outputs carry a
**point-dependent** pseudorandom offset (private-constrained style, e.g. a shift
`f((x,w), β) = (1 − C(x,w))·PRF_β(x,w)` of the AMR26 shift-hiding PRF, hidden by Lemma 14).
That does not touch the remaining crux, a public evaluator for `O`. What tree encodings do add
there: `Eval` is laconic (depth `poly(log λ, log δ)`), so `O` can be a polylog-depth circuit if
that ever helps an obfuscation step.

## 6. (a) Tree-structured hybrids: inside the affine-syzygy barrier

The natural witness-tree hybrid uses prefix keys `v_ρ = v ∏_{i<|ρ|}(I ⊗ P_{ρ_i})`, which
determine the master on the subtree `ρ`, and the subtree encodings
`c_ρ = v_ρ − sᵀ(h_ρᵀ ⊗ G) + noise` (path expansion of `c`). A hop "release `v_ρ`" is safe only if
`sᵀ(h_ρᵀ ⊗ G)` is simulatable, i.e. if the subtree digest `h_ρ = 0`.
* With **exact** truth-table hashing (`sum_paths_prod`), `h_ρ = Σ_{α ⊒ ρ} c_α φ(α)` is `0` on a
  witness-free subtree, and nonzero with high probability over `D` otherwise (distinct paths give
  distinct monomials in the entries of `D_0, D_1`; Schwartz–Zippel). Exact hashing of a
  circuit's truth table therefore decides SAT in randomized polynomial time. It exists only for
  read-once branching programs, which are in P.
* With **tree-encoded** circuits the leaves are the flattened `MBP_φ(α)`, which are nonzero on
  false leaves, `h_ρ ≠ 0`, and `h_ρᵀ ⊗ sᵀG` leaks `s` (`root_encoding_leak`).

More fundamentally, a tree-encoding WE ciphertext is **laconic**: its length `N` depends on
`λ, d` and the depth bound, not on `|φ|`. Its decryption is linear in the data (`z H`, `c P_w`)
with `log B_H ≈ dδ log(tmn⁴)`. The barrier statement `φ_real` of `pq-we-affine-syzygy-barrier`
(an OR of `4M` PRG checks) has depth `depth(Prg) + O(log M)`, so a laconic scheme supports it at
fixed `N` while `|φ_real| = 4M|Prg|` grows. **A tree-encoding WE with data-only witness-indexed
hybrids is impossible.** The laconic property, the paper's main selling point, is exactly the
"succinct" hypothesis of that barrier. A tree-encoding design must change keys across hybrids
(function hiding, section 4: 2-key, hence iO) or decrypt non-linearly (rounding, `G^{-1}`; the
normal form of open PR #36 shows these keep the cancellation-term requirement).

## 7. (b) The split lemma (relay for agent (k))

Tree encodings have **one** secret `s`. All path structure is in public short matrices
`P_b, Q_{y,b}`. The split lemma of PR #42 is about **products of secrets** along GGH15 paths
(the shared suffix factor `T_y`). So "correlated copy vs independent copy" has no tree-encoding
analogue: copying a node of the tree copies public matrices only. Nothing in AMR26 proves the split.
One possibly useful pointer: decomposed LWE is the assumption "LWE on `A_i B_j` with public short
`B_j` and a gadget planted on the diagonal". It allows public short relations next to LWE samples
because the secret is never given on `A_i` itself. A plain-LWE (or decomposed-LWE) proof of the
split would have to keep the GGH15 preimages in that shape, with the published short matrices
only multiplying matrices on which the secret has no samples.

## 8. Verdict and the precise missing lemma

* T1 (publish the tree-encoding root): dead, `root_encoding_leak`.
* T2 (universal tree): dead by itself. Needs the masking of section 5 plus a public evaluator.
* T3 (shift-hiding PRF + evaluator): the crux, in laconic form.
* T4 (two shifted keys): dead (same-`crs` gadget leak) or an evaluation collision (two `crs`).
* §4.4 circular route: the naive KDM assumption is false. The consistent version is iO-type,
  statement-dependent and not falsifiable.
* (a) tree hybrids: excluded for data-only proofs by the affine-syzygy barrier (laconic ⇒
  succinct).
* (b) split lemma: no analogue.

**Missing lemma (read-once form of the evaluation crux).** Let `pk ← TreeSetup`,
`z = sᵀZ + e`, `M ← Z_q^{n×mn²}` secret, `v = sᵀ G M`, and `P_w = ∏_{i<128}(I ⊗ P_{w_i}) R`.
Find an efficient randomized `Rep(v)` and a simulator `Sim` such that (1) from `Rep(v)` and `w`
one computes `⌊v P_w⌉_p ± 1` for every `w ∈ {0,1}^128`; and (2) for every false `φ`,
`(pk, z, c = sᵀG(M − h_φᵀ ⊗ I) + e', Rep(v)) ≈ (pk, z, c, Sim(pk, z, c, φ))` under
`Def_DecomposedLWE`/LWE at about `2^{-384}` advantage per hop, with at most about `2^128` hops,
each using only the local fact `φ(w) = 0`. Conditions (1) and (2) together give WE for
`Def_WE_CircuitSAT` (decrypt with `⌊v P_w⌉ − ⌊(c P_w + z-terms)⌉ = φ(w)⌊sᵀG⌉`). By section 6, the
hybrid of (2) cannot be data-only with linear decryption. By section 4, it cannot use a 2-key
shift-hiding step. These are the two shapes that tree encodings would naturally provide.

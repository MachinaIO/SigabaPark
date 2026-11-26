---
title: Lean vocabulary for the GGH15 WE candidates (CVW18 Construction 5.1, masked and positional laws) and the three open lemmas as theorem nodes
refs: [definition:GGH15, definition:WE_MaskedGGH15, definition:WE_CircuitSAT, note:pq-we-witness-prf-masked-evaluator, note:pq-we-ggh15-row-partitioned-trapdoors, note:pq-we-split-lemma-attempts, note:pq-we-hybrid-count-barrier, theorem:AdvancedEncryption.WE.Hybrid.hardAt_chain, theorem:AdvancedEncryption.WE.Gray.adjacent_one_bit, theorem:AdvancedEncryption.WE.GGH15.path_identity, theorem:AdvancedEncryption.WE.GGH15.encode_path_identity, theorem:AdvancedEncryption.WE.GGH15.gammaTensorDiag_mul, theorem:AdvancedEncryption.WE.MaskedGGH15.cnfMat_pathProd_eq_zero_iff, theorem:AdvancedEncryption.WE.MaskedGGH15.pathProd_maskedSecret, theorem:AdvancedEncryption.WE.MaskedGGH15.leftDiff_mul_maskedSecret, theorem:AdvancedEncryption.WE.MaskedGGH15.masked_decrypt, theorem:AdvancedEncryption.WE.MaskedGGH15.plr_hop, theorem:AdvancedEncryption.WE.MaskedGGH15.masked_two_vector, theorem:AdvancedEncryption.WE.MaskedGGH15.overcomplete_cut]
tags: [witness-encryption, vocabulary, open-problem, candidate]
---
Design-AI sub-task (o) on `Def_WE_CircuitSAT`. The GGH15-based WE candidates of the DAG reduce to
three lemmas that were so far stated only in prose: the masked two-vector lemma (note
`pq-we-witness-prf-masked-evaluator`, §6, PR #45), the PLR hop (note
`pq-we-masked-evaluator-mechanisms`, §3, open PR #54) and the overcomplete cut lemma (note
`pq-we-masked-overcomplete-leaf`, §10, open PR #55). This PR adds the Lean vocabulary needed to
state them, the three statements as **open theorem nodes**, and seven helper facts with complete
proofs that show the definitions compute what the notes say. PRs #54 and #55 are open at the time
of writing and are cited by number only. The exact preimage identities of
`pq-we-split-lemma-attempts` (`AdvancedEncryption.WE.Split.*`) apply verbatim to `preimageRows`,
which is `Trapdoor.preimage` after a renumbering of the rows.

Source: Chen–Vaikuntanathan–Wee, *GGH15 Beyond Permutation Branching Programs: Proofs, Attacks,
and Candidates*, CRYPTO 2018, ePrint 2018/360 ("CVW18"), read from the full text. Numbers below
refer to it.

## 1. `Def_GGH15` (namespace `AdvancedEncryption.WE.GGH15`)

* `encode p S A_h` is **CVW18 Construction 5.1** (`ggh.encode`) for already computed secrets
  `Ŝ_{i,b} = γ(M_{i,b}, S_{i,b})` and a given top matrix `A_h ∈ Z_q^{t×m}`: uniform
  `A_0, …, A_{h−1}`, errors `E_{i,b} ← χ^{t×m}` (`χ = D_{Z,χ}`), and
  `D_{i,b} ← A_{i−1}^{-1}(Ŝ_{i,b} A_i + E_{i,b}, σ)` drawn from the exact coset Gaussian
  (`Trapdoor.preimage` of `SigabaNeoStd`). It returns all level matrices; each scheme publishes
  what it publishes (`J·A_0`, …). Levels are `Fin h` (CVW18's level `i` is index `i − 1`).
* Rows of the level matrices are indexed by any finite type `ι` (`t = |ι|`), so the block shapes
  are `Matrix.fromBlocks` of Kronecker products. Preimages renumber the rows by
  `Fintype.equivFin`, which changes no coset.
* `pathProd X x = X_{0,x_0} ⋯ X_{h−1,x_{h−1}}`; `gammaTensor`, `gammaDiag`, `gammaTensorDiag` are
  the three γ functions of §5.1.
* `CloseAt D₀ D₁ k L W`: every machine `A` has `2^k · gain ≤ L² · (cost A + W)`, gain the squared
  advantage of `Problem.decision D₀ D₁`. With `L = 1, W = 0` it is `Problem.HardAt k`. It is the
  shape that a reduction from a `k`-bit premise produces, and the shape consumed by
  `AdvancedEncryption.WE.Hybrid.hardAt_chain`.

## 2. `Def_WE_MaskedGGH15` (namespace `AdvancedEncryption.WE.MaskedGGH15`)

* **CNF BP** (CVW18 Construction 6.4): `Ψ j i b = true` iff the literal `x_i = b` is in clause
  `j`; `cnfMat Ψ i b = diag_j([¬Ψ j i b])`; `Sat Ψ x`. Tseitin is not formalized: `Ψ` is any CNF
  over the `h` level variables (witness bits and gate bits, as in PR #45).
* **Rows** `(Fin c × Fin dR) ⊕ ((Fin w × Fin n') ⊕ Fin n)`: comparator/mask block, constraint
  block (one `n'`-block per clause), CPRF block. **Secret** `maskedSecret P R M S' S =
  diag(P ⊗ R, M ⊗ S', S)`. Secrets `R_i, S'_{i,b}, S_{i,b}` are independent `D_{Z,σ}` matrices
  (CVW18 Definition 3).
* **Left matrices** `leftO st r₀ = (1_n ⊗ (e_st ⊗ r₀) | 0 | I_n)` and
  `leftC j_C s'₀ = (0 | 1_n ⊗ (j_C ⊗ s'₀) | I_n)`, CVW18's `J = (J' | I_n)` of Theorem 5.7 with the
  rank-one difference of PR #45 attack 2. `r₀, j_C, s'₀` are public scheme parameters. **Mask**
  `maskOf r₀ R A^{mask} = (r₀ R_*) A^{mask}`, `R_* = R_0 ⋯ R_{h−1}`.
* **Masked candidate** (PR #45 §5, `c = 1`, `P = 1`): `maskedReal` / `maskedIdeal` are the two
  sides of the masked two-vector lemma, `(J_O A_0, J_C A_0, {D_{i,b}}, mask or uniform)`;
  `maskedCiphertext μ` is the WE ciphertext with component `⌊mask⌉₂ ⊕ μ` (coordinatewise most
  significant bit).
* **Positional candidate** (PR #54 §3, `c = 3`): `positionalView … t`, `t ∈ [0, 2^h]`. Comparator
  `cmpMat h t i b` in reflected Gray order (states lt/eq/gt; eq moves by the rank interval of the
  extended prefix, `cmpFromEq`), start state `cmpStart` (eq if `t < 2^h`, else lt), top matrix
  `positionalTop` with `mask'` on lt rows and `mask` on eq/gt rows, uniform `A^{con}, A^{bot}`. In
  hybrid `t` exactly the paths of Gray rank `< t` end in lt. The definition was checked
  exhaustively against the Gray rank for `h ≤ 6`, every `t ≤ 2^h` and every path (script, not
  Lean); `grayCode h t` is the path of rank `t` (`t ⊕ ⌊t/2⌋`, as in
  `AdvancedEncryption.WE.Gray.adjacent_one_bit`).
* **Cut hybrid** (PR #55 §6, §10): `cutView … L ideal`, rows without the CPRF block, `L` levels;
  `ClauseWithin`, `FirstUnsat`.
* **Regime** (CVW18 Theorem 5.7, Lemmas 3.9, 4.4, 5.3) and the explicit losses `hopLoss h t =
  64(h+1)²(t+1)` and `simCost h t m q k = 2^30 (h+1)² (t+m+1)^6 (⌈log q⌉+k+1)^4`.

## 3. Helper facts (complete proofs in this PR)

* `GGH15.path_identity`: CVW18 Eq. (10) as an exact identity over any commutative ring,
  `A_0 D_x = Ŝ_x A_h + Σ_j Ŝ_{<j} E_{j} D_{>j}`, from the per-level equations.
* `GGH15.encode_path_identity`: every output of `encode` satisfies those equations mod `q`, so the
  identity holds on the support of Construction 5.1.
* `GGH15.gammaTensorDiag_mul`: `γ_⊗diag` is multiplicatively homomorphic.
* `MaskedGGH15.cnfMat_pathProd_eq_zero_iff`: `M_x = 0 ⟺ Ψ(x) = 1` (Construction 6.4).
* `MaskedGGH15.pathProd_maskedSecret`: path secrets are `diag(P_x ⊗ R_*, M_x ⊗ S'_x, S_x)`.
* `MaskedGGH15.leftDiff_mul_maskedSecret`: `u_O − u_C` reads `(e_st P) ⊗ (r₀R)` and
  `−(j_C M) ⊗ (s'₀S')`; the CPRF block cancels.
* `MaskedGGH15.masked_decrypt`: on every witness `x`,
  `u_O D_x − u_C D_x = 1_n ⊗ mask + (J_O − J_C)·err_x` exactly mod `q`. The masked candidate's
  decryption is canonical, so the laws above are the ones the notes describe.

## 4. The open targets

All three take a decision-LWE premise `LWE.decision.HardAt pL k` (the standard LWE of
`SigabaNeoStd`: uniform public matrix, uniform secret, `D_{Z,χ}` errors, modulus `q`) and the
regime, and conclude `CloseAt … k L W`.

1. **`plr_hop`** (PR #54). For `t < 2^h` with `¬ Sat Ψ (grayCode h t)`: hybrids `t` and `t + 1`
   of `positionalView` are close with `L = hopLoss(h, 3dR + wn' + n)`, i.e. `poly(h)·ε_LWE`. With
   `hardAt_chain`, `2^h` such hops (`L` grows by `2^h`) connect the real view to hybrid `2^h`, in
   which `mask` occurs only in the challenge component.
2. **`masked_two_vector`** (PR #45). For unsatisfiable `Ψ`: `maskedReal ≈ maskedIdeal` with
   `L = 2^h · hopLoss(h, dR + wn' + n)`, the witness-indexed loss PR #45 allows.
3. **`overcomplete_cut`** (PR #55). For `1 ≤ L ≤ h`, `FirstUnsat Ψ L` and
   `dR + wn' < 2^{L−1}`: `cutView … false ≈ cutView … true` with `L = 2^L · hopLoss(L, dR + wn')`.

## 5. Modelling choices and caveats (read before proving or refuting)

* **Ideal trapdoors.** `A_i` uniform and `D` from the exact coset Gaussian is CVW18's distribution
  up to the statistical error of `TrapSam` and `SamplePre` [GPV08, MP12] (`Trapdoor.Sampler`).
  `A_h ∈ Z_q^{t×m}` as in Construction 5.1, not the reduced `A_h` of Remark 5.4.
* **Explicit constants.** `hopLoss`, `simCost` and the `Regime` conditions are generous choices
  for a concrete reading of "`poly(h)·ε_LWE`". `Regime.stat` (`k ≤ n_L`) puts statistical terms
  below `2^{−k}`. A proof that needs other constants or conditions should state a variant node
  (the DAG is append-only) and explain why in a note. Views are encoded as bits by
  `encodeTuple`; nothing depends on the particular encoding beyond its efficiency.
* **Non-degenerate left vectors.** All three statements assume `r₀ ≠ 0`, `s'₀ ≠ 0` and
  `j_C k ≠ 0` for every clause. Without this the PLR hop is false: with `j_C = 0`, the value
  `u_O D_t − u_C D_t` of path `t` is `(r₀R_*)·mask` in hybrid `t` and `(r₀R_*)·mask'` in hybrid
  `t + 1`, and the challenge component tells them apart.
* **Positional mask secrets are bit-independent.** PR #54 writes `R_{i,b}` "fresh per (level,
  bit)". Then the witness-path value is `r₀ R_{z} mask` with a path-dependent `R_z`, so no
  ciphertext component "`⌊mask⌉ + μ`" decrypts. This PR uses `P_{i,b} ⊗ R_i` with
  bit-independent `R_i`, as in PR #45, and the challenge component `(r₀ R_*)·mask`, which
  `masked_decrypt` (for `c = 1`) shows is the canonical key. Consequence for PR #55 §11: with
  bit-independent `R_i`, `D_{i,0} − D_{i,1}` annihilates the absorbing lt/gt comparator rows
  (`(P_{i,0} − P_{i,1}) ⊗ R_i` vanishes there), so the "no mask-block zero encodings" remark of
  §11 does not apply to this form. A bit-dependent variant needs its own definition node and a
  different decryption key.
* **Hop view.** The hop view contains the challenge `(r₀R_*)·mask`, so the hops compose into a
  WE proof. The start state, and with it `J_O`, depends on `t`: it is lt for `t = 2^h`.
* **Cut hybrid, literal reading.** "Every level-`L` target replaced by an independent uniform
  matrix" is taken literally: the mask block, the first-`L` clause blocks (including the dead
  entries, whose real target is `E`) and the other clause blocks are all replaced. The leaf-first
  result of §6 step 2 is modelled by `(M_{L,b})_{kk}·U_{b,k} + E` on the first-`L` clause blocks.
  Levels below `L` are dropped, as in §10 (`(W, D_1, …, D_L)`).
* **Statement dependence.** `masked_two_vector` and `overcomplete_cut` are statement-dependent
  (false for satisfiable `Ψ`, resp. satisfiable first-`L` sub-CNF). By
  `pq-we-hybrid-count-barrier` they need super-polynomially many hops, which their losses allow.
  `plr_hop` is local and falsifiable (`¬ Sat Ψ (grayCode h t)` is checkable).

## 6. Suggested next steps

* Prove `plr_hop` for `h = 2` and two clauses (PR #55 §11 predicts it follows from the point
  separator `hop_hiding_of_point_separator` when `2^h ≤ w n'`). A variant with `h` fixed small is
  a fair first node.
* Prove the comparator lemma: the start row of `pathProd (cmpMat h t) x` is `e_lt`, `e_eq` or
  `e_gt` according to `grayRank x < t`, `= t` or `> t`.
* State CVW18 Lemma 4.4 and Theorem 5.7 / Corollary 5.9 with this vocabulary. They are the
  single-left-vector baselines from which the two-vector statements depart (Remark 5.8).

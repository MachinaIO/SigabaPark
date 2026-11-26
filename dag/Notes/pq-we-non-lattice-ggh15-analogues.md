---
title: Non-lattice GGH15 analogues for WE - code/LPN chains (noise compounding), rank metric, group-action, tensor-isomorphism and MQ walks (verdicts and exact gaps)
refs: [definition:WE_CircuitSAT, definition:WE_CircuitSAT_Capped, definition:GGH15, note:pq-we-non-lattice-algebras, note:pq-we-exotic-algebraic-structures, note:pq-we-direct-algebraic-languages, note:pq-we-hybrid-count-barrier, note:pq-we-affine-syzygy-barrier, note:pq-we-evaluation-oracle-crux, note:pq-we-shallow-split-arrangements, note:pq-we-native-hop-designs, note:pq-we-exposed-root-reachable-lemma, theorem:AdvancedEncryption.WE.Codes.card_le_of_sparse_preimages, theorem:AdvancedEncryption.WE.Exotic.rank_support_mono, theorem:AdvancedEncryption.WE.Exotic.canonical_linear_test_hsp, theorem:AdvancedEncryption.WE.Direct.nand_gadget_affine_closure, theorem:AdvancedEncryption.WE.NonLattice.parity_bias_prod, theorem:AdvancedEncryption.WE.NonLattice.chain_noise_bias, theorem:AdvancedEncryption.WE.NonLattice.abelian_path_rectangle, theorem:AdvancedEncryption.WE.NonLattice.kilian_mixed_telescope]
tags: [witness-encryption, barrier, dead-end, strategy]
---
Design-AI sub-task on `Def_WE_CircuitSAT` / `Def_WE_CircuitSAT_Capped` (NAND Circuit-SAT, 128-bit
witness, `2^12` gates, `λ = κ = 128`, cost `≤ 2^100`). The question is whether a post-quantum
assumption **other than lattices** can be the *main* ingredient of a direct WE, i.e. supply the
four things the lattice frontier (`pq-we-native-hop-designs`, `pq-we-exposed-root-reachable-lemma`,
and the point-insertion analysis of open PR #113) gets from LWE and GGH15:

* (i) a **non-additive** (multiplicative / compositional) encoding of a branching program (BP) or
  circuit evaluation, so that the affine closure attack of `pq-we-direct-algebraic-languages`
  (`AdvancedEncryption.WE.Direct.nand_gadget_affine_closure`) does not apply;
* (ii) public per-bit encodings that compose along a witness path, i.e. a preimage / trapdoor
  sampler or a substitute;
* (iii) a per-hop indistinguishability step that is an instance of the assumption, for the
  `~2^128`-hop hybrid forced by `pq-we-hybrid-count-barrier`;
* (iv) canonical decryption.

This note continues `pq-we-non-lattice-algebras` and `pq-we-exotic-algebraic-structures` (which
judged the algebras as sources of *linear-test* or BGG+-type structure) and does not repeat them:
here every family is tested as a **GGH15-type product chain**. Lattice + other combinations are
out of scope (another sub-task). Four lemmas are theorem nodes with complete Lean proofs (Mathlib
only): `AdvancedEncryption.WE.NonLattice.{parity_bias_prod, chain_noise_bias,
abelian_path_rectangle, kilian_mixed_telescope}`. Everything else is informal, checked step by step
by the submitting agent; heuristic steps are marked as such. No second model was used.

## 0. Bottom line

| Family | (i) product | (ii) composable public encodings | (iii) per-hop instance | Verdict |
| --- | --- | --- | --- | --- |
| Hamming codes / LPN (binary, `F_q`, ring, dual) | sparse matrix products | CFS-type Goppa trapdoor at the optimal weight `ρ ≈ n / log₂ N` (high-rate Goppa codes are distinguishable); Wave only at high weight | **yes**: LPN with the next matrix as secret + code smoothing, exactly CVW18-shaped | **dead by noise compounding**: depth `L ≤ 50 log₂(2N+2) / k'` (§1) |
| Rank metric | `F`-valued products, no noise growth | free (trapdoor-less) once `N ≥ nm` | broken: composability forces one global error support, then a bilinear linearization recovers `S_1 S_0⁻¹` (§2) | dead |
| Group actions (CSIDH, CSI-FiSh; isogeny graphs with `End` trapdoors) | width 1: affine collapse (Lean); width > 1: clear offsets | edges are clear offsets, hence invertible | none needed / none available | dead: the compiler would decide SAT by graph connectivity (§3, §6) |
| Tensor / code / matrix-code isomorphism, ATFE | Kilian intertwining `P_j⁻¹ M P_{j+1}` | yes, noiseless | none: hardness lives in the *unlabeled* mode, labeled tuples are linear algebra | dead (§4) |
| Multivariate (iterated quadratic maps, IP) | composition of maps on points | interpolation (planted collisions) | QUAD appears, but the reduction cannot plant the merges at the challenge point | dead for read-many; read-once is the evaluation-oracle crux (§5) |
| Goldreich local PRGs | — | — | PRG only | no ingredient beyond a PRG (§7) |

**Best non-lattice candidate: the code/LPN GGH15 chain (§1).** It is the only family where (i),
(ii) and (iii) all exist in the literature in the right shape. Its gap is **quantitative and
exact**: with LPN security `k'` bits per level and a cost budget `2^100`, the chain can have at
most `50 log₂(2N + 2) / k'` levels (`≈ 74` for `k' = 68`, `≈ 15` for the `~2^{384}`-type premises
of the hybrid count), while any BP for the problem needs `≥ 128` levels read-once (and width
`≥ 2^64`, `pq-we-shallow-split-arrangements`) or thousands of levels read-many (`L = 4352` gives
decryption bias `≤ 2^{-2930}`). No non-lattice family supplies a composable, non-canonical noise;
in the families examined this is exactly what lattices add.

## 1. Codes / LPN: the GGH15 chain and its noise compounding

### 1.1 Scheme

Over `F_2` (the `F_q` case is the same with `1 − 2τ` replaced by `1 − qτ/(q − 1)`): matrices
`A_i ∈ F_2^{n×N}` with trapdoors, and for each level `i` and bit `b`
`D_{i,b} ← A_i^{-1}(S_{i,b} A_{i+1} + E_{i,b})`, a *sparse* preimage (column weight `ρ`), with
`E_{i,b}` Bernoulli(`τ`) and `S_{i,b}` invertible (for hiding, `S_{i,b} = M_{i,b} ⊗ R_{i,b}` as in
CVW18, `R` an LPN-type secret). Decryption reads `A_1 D_{1,w_1} ⋯ D_{L,w_L}`:

`A_1 D_w = S_w A_{L+1} + Σ_i S_{<i} E_{i,w_i} D_{>i}`,

and one output bit carries the noise `Σ_i r_iᵀ E_i h_i` with `r_i` a row of `S_{<i}` (nonzero,
`S` invertible) and `h_i` a column of `D_{>i} = D_{i+1} ⋯ D_L`.

### 1.2 What exists

* **(iii) The per-hop step is a genuine LPN instance.** The CVW18 move "`S_{i,b} A_{i+1} + E` is
  pseudorandom for hidden uniform `A_{i+1}`" is LPN with the columns of `A_{i+1}` as secrets and
  the rows of `S_{i,b}` as (hidden) public vectors; secrets from the noise distribution are as
  hard as uniform ones (Applebaum–Cash–Peikert–Sahai, CRYPTO 2009). The second move, "a sparse
  preimage of a uniform target looks like a random sparse vector with its syndrome", is code
  smoothing (leftover hash): it needs `ρ log₂(N/ρ) ≳ n + 2λ`, which is the same regime as
  `AdvancedEncryption.WE.Codes.card_le_of_sparse_preimages`. So the hop structure transports.
* **(ii) Trapdoor preimages.** The weight bound `ρ ≥ n / log₂(2N + 2)` of
  `card_le_of_sparse_preimages` is met, up to a constant, by **CFS** (Courtois–Finiasz–Sendrier,
  Asiacrypt 2001): Goppa codes of length `N = 2^m`, `n = mt`, decode a random syndrome with weight
  `t = n / log₂ N` with probability `≈ 1/t!`. Its premise (indistinguishability of Goppa codes) is
  **false in this regime**: the high-rate Goppa codes CFS needs are distinguished from random
  codes in polynomial time (Faugère–Gauthier-Umaña–Otmani–Perret–Tillich, IEEE TIT 2013). Wave
  (Debris-Alazard–Sendrier–Tillich, Asiacrypt 2019) samples uniform preimages of arbitrary
  syndromes, but only at **large** ternary weight (above the typical weight `2N/3`), where one
  inner product `⟨e, h⟩` with `wt(h) = Θ(N)` already has bias `≈ (1 − 3τ/2)^{Θ(N)}`: one level
  saturates. The LPN "trapdoors" of Kiltz–Masny–Pietrzak (PKC 2014) and Yu–Zhang (CRYPTO 2016)
  invert the LPN function for CCA decryption; they do not sample preimages of the syndrome map.
  Rank-metric preimage sampling (RankSign) is broken (Debris-Alazard–Tillich, Asiacrypt 2018).

### 1.3 Noise compounding (Lean)

**`AdvancedEncryption.WE.NonLattice.parity_bias_prod`.** For independent Bernoulli(`τ`) bits
`x ∈ F_2^I` and any `c`, `E[(-1)^{⟨c, x⟩}] = Π_i (1 if c_i = 0 else 1 − 2τ) = (1 − 2τ)^{wt c}`.

**`AdvancedEncryption.WE.NonLattice.chain_noise_bias`.** For `L` independent Bernoulli(`τ`) noise
matrices `E_i` (flattened to `Fin L × Fin m × Fin n`), the bilinear noise `Σ_i r_iᵀ E_i h_i` has
bias **exactly** `(1 − 2τ)^{Σ_i wt(r_i) wt(h_i)}`, and if every `r_i ≠ 0`, `wt(h_i) ≥ ρ` and
`0 ≤ τ ≤ 1/2`, this is `≤ (1 − 2τ)^{L ρ}`.

Applying it to the chain treats the `E_{i,w_i}` as independent of the `(r_i, h_i)`. This is the
usual fresh-noise heuristic of GGH15 noise analyses: `h_i` involves `D_{i+1}, …, D_L` only, but
`D_j` depends on `E_j`, which also occurs in the term `j`. Rigorously the identity bounds the
`i = 1` term alone (`E_1` enters only `D_1`, which is not in the noise), giving bias
`≤ (1 − 2τ)^ρ`; the `L`-level bound is the heuristic product.

### 1.4 The depth bound

* Weight: `h_i` is (up to noise) a preimage under `A_{i+1}` of a pseudorandom target, so for all
  but a `2^{−n/2}` fraction of targets `ρ ≥ n / (2 log₂(2N + 2))` (counting in
  `card_le_of_sparse_preimages`).
* LPN security: low-noise LPN is solved by Gaussian elimination on `n` samples, all noise-free
  with probability `(1 − τ)^n ≤ e^{−τn}`, at cost `≈ n^3 e^{τn}`. A level secure to `k` bits needs
  `τ n ≥ k' ln 2` with `k' = k − 3 log₂ n` (better attacks only raise the requirement).
* Bias: `β ≤ (1 − 2τ)^{Lρ} ≤ e^{−2τLρ} ≤ 2^{−k' L / log₂(2N+2)}`. Reading one bit of bias `β`
  needs `≈ β^{−2}` independent bits, each a full chain evaluation, so decryption costs
  `≥ 2^{2 k' L / log₂(2N+2)}`.

With cost `≤ 2^100` (so `N ≤ 2^100`, `log₂(2N+2) ≈ 101`): **`L ≤ 5050 / k'`**. Concretely

| `k` (per-level LPN security) | `k'` (`n ≈ 2^{20}`) | max levels `L` | bias at `L = 128` | bias at `L = 4352` |
| --- | --- | --- | --- | --- |
| 128 | 68 | 74 | `2^{−86}` | `2^{−2930}` |
| 384 (hybrid-count premises) | 324 | 15 | `2^{−410}` | `2^{−13961}` |

A BP for the problem needs `L ≥ 128` levels when read-once, with width `≥ 2^{64}` for
single-prefix-flip walks (`pq-we-shallow-split-arrangements`), and thousands of levels when
read-many (`L = 4352` for the 4096-gate circuit plus input layers). Reading `t` bits per level
(`2^t` matrices per level, `L = 128/t`) fits the depth bound only for read-once programs, where
the width bound applies. Lattices escape because their noise grows additively in a norm with a
super-polynomial ceiling `q`; the Hamming ceiling is the noise rate `1/2`.

**Verdict: dead.** Exact gap: a Hamming-metric GGH15 chain with `L ≥ 128` needs
`2τLρ ≲ 50 ln 2` together with `τn ≳ k' ln 2` and `ρ ≳ n / (2 log₂ N)`, which are incompatible
for `k' ≥ 40`. Closing it requires LPN that is secure with `τ n = O(1)` (false) or preimages of
weight `o(n / log N)` (impossible by counting).

## 2. Rank metric: no compounding, but a broken hop

`AdvancedEncryption.WE.Exotic.rank_support_mono` says that `F`-valued matrices do not enlarge the
error support in `K = F_{q^m}`. So a rank-metric chain `A_i D_{i,b} = S_{i,b} A_{i+1} + E_{i,b}`
with `D, S` over `F` has total noise support `⊆ Σ_i supp(E_i)`, of dimension `≤ L r`, no matter
how long the chain: (i) and (iv) look fine (with `m > 2Lr`). The problems:

* **Composability forces one global support per noise matrix.** An entry of
  `S_{<i} E_i D_{>i}` is an `F`-combination of many entries of `E_i`, so its support is the sum
  of their supports. With per-entry (per-sample) supports, as in rank-metric LWE, this is the
  whole of `K` after one level; with `D` entries in a `d`-dimensional subspace the support grows
  like `r d^L`, the Hamming situation again. The only composable choice is: all entries of `E_i`
  in one `r`-dimensional subspace `V_i` (the rank-support-learning setting), and `F`-valued
  `D, S`.
* **`F`-valued preimages are free.** `A d = t` with `A ∈ K^{n×N}`, `d ∈ F^N` is `nm` linear
  equations over `F`, solvable for every `t` once `N ≥ nm`, with no trapdoor. (ii) holds trivially,
  so the encodings carry no one-wayness at all.
* **The hop is broken (heuristic linearization).** With `Y_b = S_b A + E_b` (`b = 0, 1`, same
  hidden `A`), `Y_1 − M Y_0 = E_1 − M E_0` has all entries in `W = V_0 + V_1` (dimension `2r`)
  for `M = S_1 S_0^{-1} ∈ F^{n×n}`. Writing an annihilator of `W` in systematic form gives, for
  each of the `m − 2r` annihilator rows, `nN` equations bilinear in `M` and `2r` unknowns, with
  `(n² + 1)(2r + 1)` monomials. Linearization solves it when `N ≥ n(2r + 1)`, which is implied by
  `N ≥ nm` (and `m > 2r`). This assumes the linearized system has generic rank (not proved), as in
  the Debris-Alazard–Tillich attacks on rank support learning (Asiacrypt 2018). It recovers
  `S_1 S_0^{-1}`, which distinguishes the CVW18-type pair from uniform; with monomial `S` (the
  only way to keep row-wise supports) a single row difference of rank `≤ 2r` instead of `m`
  distinguishes directly.

**Verdict: dead.** Exact gap: composability needs a single error support per level, and a single
support plus two encodings under one hidden `A` is linearizable.

## 3. Group actions (CSIDH, CSI-FiSh, isogeny graphs)

**Width one collapses (Lean).** `AdvancedEncryption.WE.NonLattice.abelian_path_rectangle`: for a
state-free BP over an abelian group (class-group exponents), the path label
`P(v) = Σ_j f_j(v_{var j})` satisfies `P(00) + P(11) = P(01) + P(10)` in any two positions,
for any reading order and any number of reads; `P` is affine in the witness. Commutativity does
not "kill" mix-and-match, it makes mix-and-match an identity, and an affine gate predicate is
exactly what `nand_gadget_affine_closure` breaks.

**Width above one needs clear offsets, which are invertible.** With states, the path label is
`Σ_j λ_j(state_j, bit)`, a general function. But the decryptor must move from the set element of
node `(j, s)` to that of `(j + 1, t)`. In the generic group-action model the only ways are a
public target (no gating) or a group element known in the clear (combining two hidden ones is the
parallelization problem; `pq-we-non-lattice-algebras` §1). A clear offset `g` gives `X' = g ⋆ X`
**and** `X = g^{-1} ⋆ X'`: every published transition can be walked backwards. So the set of
computable nodes is the **undirected** connected component of the start node in the public-edge
graph. If the key is the accept node's element:

* correctness for satisfiable `φ` needs accept in that component;
* security for unsatisfiable `φ` needs accept outside it (otherwise the adversary walks there in
  time linear in the graph).

So a statement-independent compiler `φ ↦ graph` with both properties decides Circuit-SAT by
undirected connectivity, in polynomial time. **No such compiler exists unless P = NP.**
CSI-FiSh (known class group) only makes more offsets computable. Trapdoors from known endomorphism
rings (SQIsign / KLPT-type, higher-dimensional representations) let the *encryptor* build
isogenies between arbitrary curves, which supplies (ii); but the published codomains are curves
with canonical labels (`j`-invariants), so §6 applies.

**Verdict: dead.** (iii) is moot: there is nothing for a per-hop group-action DDH step to hide.

## 4. Tensor, code and matrix-code isomorphism; alternating trilinear forms

Matrix-group actions are non-commutative and compose; the composition of per-bit encodings is
Kilian randomization `D_{j,b} = P_j^{-1} M_{j,b} P_{j+1}`.

**Lemma (Lean, `AdvancedEncryption.WE.NonLattice.kilian_mixed_telescope`).** In any group,
`Π_j p_j⁻¹ M_j(c_j) p_{j+1} = p_0⁻¹ (Π_j M_j(c_j)) p_L` for **every** word `c`, consistent with an
input or not.

Consequences:

* **Labeled tuples are linear algebra.** In WE the BP matrices `M_{j,b}` come from the public
  statement. The intertwining equations `P_j D_{j,b} = M_{j,b} P_{j+1}` are linear in the
  unknowns `(P_0, …, P_L)`, so the randomizers are recovered up to the commutant of the BP, in
  polynomial time. More generally, deciding whether two *labeled* matrix tuples are equivalent
  under `(X ↦ A X B)` is a linear-space-of-matrices problem solved in polynomial time (module
  isomorphism: Chistov–Ivanyos–Karpinski 1997, Brooksbank–Luks 2008). Tensor isomorphism, matrix
  code equivalence and ATFE are hard only because of the **unlabeled** mode (the hidden basis of
  the tuple, `GL_k` on the third index); an evaluator who must select the matrix for bit `b`
  needs that mode in the clear.
* **Secret factors (noiseless GGH15).** With `D_{j,b} = P_j^{-1}(M_{j,b} ⊗ R_{j,b}) P_{j+1}` and
  secret `R`, the equations become bilinear (a tensor-isomorphism-type problem), but the loop
  `D_{j,0} D_{j,1}^{-1}` is conjugate to `(M_{j,0}M_{j,1}^{-1}) ⊗ (R_{j,0}R_{j,1}^{-1})`; its
  characteristic polynomial is public, and its spectrum is the product set of the two spectra,
  which carries the public permutation structure of the BP step (for example closure under
  multiplication by the eigenvalues of a transposition). Exact data also gives the bookended value
  on all mixed inputs (lemma above), the setting of zeroizing / annihilation attacks.
* **(iii).** The registered assumptions of this family (TI, MCE, LESS-type code equivalence, ALTEQ)
  are search or decision problems on unlabeled objects. None states pseudorandomness of a labeled
  per-bit pair, which is what a per-hop step would need.

**Verdict: dead** as a main ingredient; useful for signatures only.

## 5. Multivariate: iterated quadratic maps

Scheme: random encodings `y_{j,s} ∈ F_q^m` of BP states, and public quadratic maps `F_{j,b}`
chosen uniformly subject to `F_{j,b}(y_{j−1,s}) = y_{j,δ(s,b)}` (interpolation; equivalently
`T_j ∘ Q_{j,b} ∘ T_{j+1}^{-1}` with hidden affine `T`, an isomorphism-of-polynomials disguise).
Decryption walks the point `y_{0,start}` along `w`; the key is `H(y_{L,acc})`. The maps are not
publicly invertible, so the undirected argument of §3 does not apply.

* **Correctness is exact and canonical**, which is the weakness: equal BP states get equal points.
  For a read-many BP, a forward search over mixed words with deduplication of points computes the
  set of mixed-reachable encodings with `≤ 2 · L · width` map evaluations (§6).
* **Security is a planted, statement-dependent system.** For unsatisfiable `φ`, the hidden
  `y`'s of unreachable states satisfy `y_{j,δ(s,b)} = F_{j,b}(y_{j−1,s})` with merges
  `F_{j,0}(y_s) = F_{j,1}(y_{s'})`: a polynomial system determined by the BP of `φ`.
* **(iii).** The one place a standard MQ instance appears: `(F_{j,0}(y), F_{j,1}(y))` for a hidden
  uniform `y` and random maps is the QUAD PRG with stretch 2 (Berbain–Gilbert–Patarin, Eurocrypt
  2006). A hop would replace the next-layer encodings of a dead state by uniform. But the
  reduction receives `F` and `F(y)` with `F` independent of `y`, while the scheme needs `F` to
  plant the merge `F_{j,0}(y) = F_{j,1}(y_{s'})`: either `y` (unknown) or an MQ preimage (hard).
  In GGH15 this is solved by the hidden matrix `A_{j+1}` plus trapdoor sampling one level up;
  interpolation plays the trapdoor's role but needs the point itself.
* Read-once BPs avoid mixed inputs but need width `≥ 2^{64}`; a shift-register state (the prefix
  itself) moves the whole evaluation of `φ` into the last map, which is the evaluation-oracle
  crux (`pq-we-evaluation-oracle-crux`).

**Verdict: dead** for read-many; read-once is the known crux.

## 6. A common barrier for noiseless walks (canonical labels)

§3–§5 share one shape, also covered by `AdvancedEncryption.WE.Exotic.canonical_linear_test_hsp`
for linear tests: **public deterministic transitions on objects with canonical labels** (points,
curves, matrices up to exact equality). Then the adversary computes the set
`R_{j+1} = F_{j,0}(R_j) ∪ F_{j,1}(R_j)` of labels reachable by mixed words, deduplicating equal
labels. If the scheme realizes the BP's merges (equal state, equal label), `|R_j| ≤ width` and
the search costs `≤ 2 L · width` steps. Correctness for satisfiable `φ` makes accept reachable,
and security for unsatisfiable `φ` needs it unreachable by mixed words. So the compiler's BPs
must satisfy "accept is mixed-reachable iff `φ` is satisfiable"; layered reachability is
polynomial, so such a compiler decides Circuit-SAT (P = NP), and for any other compiler some
unsatisfiable `φ` is broken by the search. If it does not realize the merges
(path-dependent labels), all accepting paths must still meet at one key, so the final map
evaluates acceptance on path labels: the evaluation-oracle crux. **Noise is what removes
canonical labels in GGH15**: lattice encodings of one state differ per path, so no deduplication
is possible. Among the families examined, Hamming noise compounds (§1) and rank noise is either
non-composable or linearizable (§2); no other family has noise at all.

## 7. Goldreich local PRGs as per-path pseudorandomness

A per-path pseudorandom value (a GGM-type tree over Goldreich's PRG, keyed by `w`) is public only
with a public seed (then nothing is hidden), and with a hidden seed its public evaluation is the
evaluation-oracle crux. Locality `D` means degree `D` in the seed bits, so decryption-side use is
covered by the degree-`D` affine-syzygy argument (`pq-we-affine-syzygy-barrier`); key-side use
is a PRG inside another scheme (`pq-we-non-lattice-algebras` §3). Nothing new.

## 8. Cost of the best candidate, and what would change the verdict

The code/LPN chain at its maximal depth (`L ≈ 15` levels for 384-bit premises) cannot even read
the 128 witness bits once; at `L = 128` decryption costs `≥ 2^{172}` with `k' = 68` (bias
`2^{−86}`): below the brute-force baseline of `Def_WE_CircuitSAT` (about `2^{188}`) but far
above the `2^{100}` cap of `Def_WE_CircuitSAT_Capped`, and that is before the `≥ 2^{64}`
read-once width and with a Goppa premise that is false in the CFS regime. A verdict change would need one of:

1. an LPN-type assumption that is secure with noise `τ n = O(1)` per level (contradicted by
   Gaussian elimination);
2. a Hamming-metric preimage sampler of weight `o(n / log N)` (contradicted by counting,
   `card_le_of_sparse_preimages`);
3. a code metric with composable noise whose error supports stay *independent* across samples
   (rank metric fails both ways, §2);
4. a falsifiable assumption on a non-commutative action that states pseudorandomness of
   *labeled* per-bit encodings with path-dependent (non-canonical) labels, i.e. a noisy tensor
   action, which would be a new assumption and in all known instances is LWE-like.

None is available. The non-lattice families can contribute PRGs, key derivation and signatures,
but not the main ingredient; the open frontier remains the lattice one (point insertion, open
PR #113).

---
title: The overcomplete projection lemma of the masked GGH15 WE candidate - the leaf dichotomy, a cut lemma beyond the width horizon, and why no projection lemma can close the gap
refs: [definition:WE, definition:WE_CircuitSAT, note:pq-we-witness-prf-masked-evaluator, note:pq-we-hybrid-count-barrier, note:pq-we-gap-structure-routes, note:pq-we-evaluation-oracle-crux, note:pq-we-ggh15-chain-verdict, note:we-circuitsat-bruteforce-explicit-cost, theorem:AdvancedEncryption.WE.Hybrid.stat_hops_carry, theorem:AdvancedEncryption.WE.MaskedLeaf.hiding_of_separator, theorem:AdvancedEncryption.WE.MaskedLeaf.mask_of_affine_relation, theorem:AdvancedEncryption.WE.MaskedLeaf.separator_iff_no_affine_relation, theorem:AdvancedEncryption.WE.MaskedLeaf.affine_relation_of_span, theorem:AdvancedEncryption.WE.MaskedLeaf.untwisted_separator_iff, theorem:AdvancedEncryption.WE.MaskedLeaf.hop_hiding_of_point_separator, theorem:AdvancedEncryption.WE.MaskedLeaf.hop_reveal_of_span]
tags: [witness-encryption, candidate, barrier, open-problem, strategy]
---
Design-AI sub-task (n) on `Def_WE_CircuitSAT`. The target is the remaining gap of the masked
γ⊗-GGH15 WE candidate of `pq-we-witness-prf-masked-evaluator` (PR #45). The analysis of its
security lemma is in open PR #49 (note `pq-we-split-lemma-attempts`, §7), which is not merged when
this note is written and is cited by PR number only. PR #49 proves the *masked two-vector lemma* when the prefix rows entering
every level are linearly independent (`2^{h−1} ≤` rows per level). It names the missing piece the
**overcomplete projection lemma** (OPL): when more prefix rows `w_x = X_x A + e_x` enter a level
than `A` has rows, preimages `D ← A^{-1}(Y)` should reveal only the projections `{w_x D}`. The
human asked us to attack OPL, starting with "overcomplete by one row", to try five ideas and to
persist. This note records the outcome. Arguments are informal except the five Lean theorems of
this PR, which have complete proofs.

**Summary.**

1. At a level where the prefix rows span (are *complete*), OPL in the exact-row form used by the
   `h = 2` proof is **vacuous**: nothing is hidden and the lemma holds trivially. "Overcomplete by
   one row" is therefore not an intermediate case, and the difficulty is not located at a level
   (§2).
2. **Leaf dichotomy (Lean).** The root-first projection proof ends with a statistical step on the
   leaf matrix. That step works **if and only if** the constraint rows `c_z` of the paths admit a
   *separator* `ℓ` (`c_z·ℓ = 1` for every path). Otherwise an affine relation `∑α_z c_z = 0`,
   `∑α_z = 1` exists, and the **noiseless projected path values determine the mask**. This always
   happens in the overcomplete regime. So no projection-type lemma, however strong, can close the
   proof there: the end step must use the GGH15 noise computationally (§3).
3. **Idea (4) answered negatively.** For *every* polynomial-width arrangement (variable order,
   twisting pattern, fan-in), the separator condition is decidable in polynomial time and
   certifies unsatisfiability. So the projection technique proves security only for instances
   whose unsatisfiability has a poly-time certificate, where WE is trivial. With bit-independent
   constraint secrets the condition is exactly a degree-0 Nullstellensatz refutation (Lean). The
   provable exponential-width versions cost at least `2^256` bits per ciphertext, against the
   brute-force baseline of about `2^188` (§4).
4. **Idea (1) gives a positive result: overcompleteness itself is harmless.** With independent
   prefix secrets and fresh noise, normal-form LWE hides the mask for any number of rows. What
   blocks the candidate is (a) the product structure of the secrets, which forces a leaf-first
   (BPR / CVW18 phase-1) induction, and (b) the zero encodings of satisfied clauses, which stop
   that induction at each clause's deepest variable (§5). Combining leaf-first, root-first and a
   one-time-pad cut gives the **cut lemma** (§6): the masked lemma holds from LWE for every CNF
   whose clauses inside the first `L` variables are already unsatisfiable, where `2^{L−1}` is at
   most the width, with **arbitrary depth and overcompleteness below level `L`**. This strictly
   extends PR #49's `h = 2` and `2^{h−1} ≤ width` results. Like every polynomial-hop result, it
   covers only instances decidable in time `2^L·poly`.
5. Ideas (2) and (3) fail for structural reasons (§7, §8). No attack on the fully twisted
   candidate was found. The bit-independent variant is broken by every short affine relation
   among unsatisfied-clause patterns, which generalizes CVW18's inclusion–exclusion attack (§9).
6. **Exact remaining gap:** the *overcomplete cut lemma* (§10). It is a computational statement
   about one level beyond the width horizon. By the leaf dichotomy it must use the noise, and by
   the hybrid-count barrier it needs super-polynomially many hops, each local to a path.

## 1. Setting and notation

Constraint secrets are those of PR #45. Levels `1..h` read the CNF variables of `Ψ_φ` once. Each
level matrix `A_i` has a mask block (secret `R_i`, the same for both bits) and one `n'`-row
constraint block per clause `k` (secret `(M_{i,b})_{kk} · S'_{i,b}`, zero when the bit satisfies
clause `k`). The CPRF block is stripped first by CVW18 phase 1, and the exposed root row is
`W = μ_0 A_0^{mask} − ∑_k j_k s'_0 A_0^{k}`. The prefix row of a prefix `x` of length `i` is

`X_x = (μ_i | ((j_k · [k alive at x] · s'_0 S'_x))_k)`, with `μ_i = r_0 R_1⋯R_i` the same for every `x`,

and the honest value is `W D_x = X_x A_i + e_x`, with GGH15 noise
`e_x = ∑_{t<i} X_{x<t} E_{t,x_t} D_{x>t}`. The path row of a full path `z` is `X_z = (μ_h | c_z)`,
where `c_z = (j ⊙ 1_{U(z)}) ⊗ s'_0 S'_z` and `U(z)` is the set of clauses that `z` falsifies. The
mask is `m = μ_h A_h^{mask}`. *Twisted* means `S'_{i,0} ≠ S'_{i,1}` (γ⊗, needed against CVW18's
inclusion–exclusion attack, PR #45 attack 1). *Untwisted* means `S'_{i,0} = S'_{i,1}`.

## 2. Complete levels make the exact-row OPL vacuous

The projection lemma (PL) of PR #49 writes `A = T^{-1}[P; H]`, with `P` the span of the prefix
rows (exact rows, known to the reduction) and `H` hidden. It removes `H`, so that `D` is Gaussian
conditioned on `P D = (T(Y + E))_P`. If the prefix rows span all of `A`'s used rows, `H` is empty
and the conditioned law **is** the real law. Nothing has to be proved and nothing is gained:
`D_{i+1,b}` reveals the whole target `Ŝ_{i+1,b} A_{i+1} + E` up to the hidden invertible
transform `X` (`preimage_row_transform` of PR #49). The next level then receives `2·rank` prefix
rows, so it is overcomplete by a factor of 2, not by one. Consequences:

* "Overcomplete by one prefix row" (`2^{i} = rows + 1`) behaves exactly like "complete". PL is
  vacuous there, and the following level is overcomplete by about `rows`. The difficulty is not
  that one level is overcomplete. It is that **from the first complete level down to the leaf
  nothing is hidden**, and the proof must end with a step on the leaf.
* So the real question is what the root-first chain leaves at the leaf. §3 answers it exactly.

(A non-vacuous form of OPL replaces the exact rows `P` by the noisy rows `w_x`:
`(W, A^{-1}(Y + E)) ≈ (W, W^{-1}(XY + E''))`. That is an evasive-LWE-shaped statement about a
*hidden* matrix. Its ideal hybrid needs preimages under the noisy rows `W`, for which nobody has a
trapdoor, so it is **not efficiently samplable**. This is escape (b) of `pq-we-gap-structure-routes`.
It is consistent with the barriers, but no LWE technique for it is known. §3 shows that even this
form would not finish the proof.)

## 3. The leaf dichotomy (Lean, complete proofs)

After phase 1 and root-first PL (with complete levels handled trivially as in §2), the leaf
matrix `A_h^{con}` is uniform and enters the view only through the projected path rows. Every
honest path value can still be computed:

`y_z = m + c_z A_h^{con} + e_z` (up to the sign convention of `c_z`).

* `AdvancedEncryption.WE.MaskedLeaf.hiding_of_separator`: if `c_z ⬝ᵥ ℓ = 1` for every path, then
  for uniform `A` the law of `(m + c_z A + e_z)_z` does not depend on `m`, for any noise `e`
  independent of `A`. The proof uses the bijection `A ↦ A + ℓ ⊗ (m − m')`. This is exactly the
  statistical leaf step of PR #49.
* `AdvancedEncryption.WE.MaskedLeaf.mask_of_affine_relation`: if `∑α_z = 1` and `∑α_z c_z = 0`,
  then `∑α_z (m + c_z A) = m` for every `A`.
* `AdvancedEncryption.WE.MaskedLeaf.separator_iff_no_affine_relation`: over a field, exactly one of
  the two holds (`0` outside or inside the affine hull of the `c_z`; dual-functional argument).
* `AdvancedEncryption.WE.MaskedLeaf.affine_relation_of_span`: if the differences `c_z − c_{z₀}`
  span the space, an affine relation exists.

**Consequences.**

* The root-first projection proof (phase 1, then PL at every level, then the statistical leaf)
  succeeds on `φ` **iff a separator exists**. Overcompleteness at intermediate levels matters only
  through this condition.
* With full twisting the path rows are generic points of the constraint space, one per path.
  Once the number of paths exceeds its dimension `K n'`, they affinely span it, and the noiseless
  projected values determine the mask. The mask survives only because the relation `α` has huge
  coefficients, so `∑α_z e_z` is not small. **Any proof in the overcomplete regime must therefore
  use the GGH15 noise as LWE noise at the end**, not only the uniformity of hidden rows. Every
  projection-type lemma, including the noisy form of §2, only rewrites the view into projections.
  It is then followed by an end step that cannot be statistical.
* This matches the hybrid-count barrier (`pq-we-hybrid-count-barrier`). Phase 1, PL and the leaf
  step form a polynomial-hop proof with efficiently samplable hybrids, so it can work only on a
  class of instances in which unsatisfiability is easy (§4).

## 4. Idea (4): can a polynomial-width arrangement avoid the problem? No. Costs.

**Twist budget.** Suppose only the levels in a set `T` are twisted. Then `s'_0 S'_z` depends only
on `z_T`, and the separator condition becomes: there are functions `g_k` in the span
`V = {z ↦ s'_0 S'_{z} ℓ}` with `∑_{k ∈ U(z)} j_k g_k(z) = 1` for all `z`.

* **Untwisted** (`T = ∅`): `AdvancedEncryption.WE.MaskedLeaf.untwisted_separator_iff` (Lean). A
  separator exists iff clause weights `λ` satisfy `∑_{k∈U(z)} λ_k = 1` for every assignment, i.e.
  `∑_k λ_k C_k ≡ 1` for the clause indicator polynomials `C_k = ∏_{lit ∈ k}(1 − lit)`. This is a
  **degree-0 Nullstellensatz refutation**, found by linear algebra. In this case the prefix rows
  have rank at most `1 + K`, so PL applies at every level and the whole proof works exactly for
  these instances. Example: for a NAND chain `g_1 = 1`, `g_2 = ¬g_1`, output `¬g_2`, the
  coefficient system has no solution (the constant and `g_1` coefficients force
  `λ_1 + λ_2 = 1` and `λ_1 + λ_2 = 0`).
* **Twisted on `|T| ≤ log₂ n'` levels**: `V` is generically every function of `z_T`, and the
  condition says that every restriction `Ψ|_{z_T = a}` has a degree-0 refutation. This is
  decidable in time `2^{|T|}·poly`.
* **Twisted on more levels (generic)**: the condition is affine non-spanning of the path rows. The
  rows are produced by a read-once branching program of width `O(K n')`, so their affine hull can
  be computed level by level, `aff(X·M_0 ∪ X·M_1)`, in polynomial time.

In every case, separator existence is a **polynomial-time-checkable certificate of
unsatisfiability**: a satisfying `z` has `c_z = 0` and kills any separator. So the projection
technique, in any polynomial-width arrangement, proves security only on a polynomial-time
certifiable subclass of the unsatisfiable instances. On that subclass the encryptor could decide
falsity itself, and WE is trivial there. This is the concrete form of `pq-we-hybrid-count-barrier`
for this candidate.

**Cost of the provable exponential-width versions.** With full twisting, a separator needs at
least as many dimensions as there are distinct path rows. Tseitin gives `h = 128 + s` variables
(`s ≤ 2^12` NAND gates), and PR #49's condition `2^{h−1} ≤` rows already requires
`N ≥ 2^{127+s} ≥ 2^{128}`. The cut lemma (§6) needs the same for general `φ`, because the first
unsatisfiable sub-CNF may involve all variables. So `m ≥ N ⌈log q⌉ ≥ 2^{128}`, and one encoding
`D_{i,b} ∈ ℤ^{m×m}` alone has more than `2^{256}` entries. The ciphertext size, and with it the
encryption time, is at least `2^{256}`. That exceeds the explicit brute-force submission
(`we-circuitsat-bruteforce-explicit-cost`, about `2^{188}`, assumption-free) by a factor of at
least `2^{68}`. **The provable versions are dominated by brute force.**

## 5. Idea (1): use LWE on the noise, not uniformity of the rows

**Positive toy (overcompleteness is harmless by itself).** Take hidden uniform `a` (one row) and
`B` (`n'` rows), and prefix rows `w_x = a + c_x B + e_x` for **any number** `T > n'` of prefixes,
with **independent** short secrets `c_x` and fresh Gaussian `e_x`. Give `D ← a^{-1}(m + e')`
(no constraint on the rows of `B`) and the challenge `m`. Then `m` is pseudorandom:

1. Normal-form multi-secret LWE with public `B` gives `(c_x B + e_x)_x ≈ uniform`, so `W` is
   independent of `a`.
2. `a` is then used only as a preimage matrix, and CVW18 Lemma 4.4 (`A^{-1}(Z + E) ≈ Gaussian`
   for a hidden `A` used nowhere else) makes `D` independent of `m`.

The noiseless values still determine `m` (§3). LWE is exactly what defeats that.

**Why the candidate is not the toy.**

* *Noise.* GGH15 noise at a level is "prefix secret × level noise": the projections are
  `c_x(U + E_{L,b}) = c_x U'`. The level noise is **absorbed** into the uniform `U'`, and the
  projections stay **exactly** linearly dependent. Only the upper-level noise `e_x D_{L,b}` breaks
  the relation. Fresh noise per prefix cannot be added to a polynomial-size encoding. Flooding the
  extra row (`w_* = ∑β_x w_x + (e_* − ∑β_x e_x)`, with large `β`) makes that row pseudorandom
  given the others, but the projections still satisfy the relation up to `∑β e_x D`, so nothing
  is gained.
* *Secrets.* `c_x = j_k s'_0 S'_x` are products. The tool for products is the BPR-style leaf-first
  induction: `S'_{i,b} A^k_i + E → U` by LWE with secret `A^k_i`. In GGH15 this is CVW18 phase 1
  on the constraint block. It needs `A^k_i` to be used only on the right, which holds after
  Lemma 4.1 has dropped the `k`-rows from `D_{i+1,b}`. Lemma 4.1 needs the next level's `k`-target
  to be uniform.
* *Zero encodings stop it.* At the deepest level `ℓ_k` of clause `k`, the satisfying bit `b*`
  has `k`-target `E` (an encoding of zero), so `A^k_{ℓ_k−1} D_{ℓ_k,b*} ≈ 0`. That row block is
  two-sided, and LWE on it is false in the clear: the hint `D_{ℓ_k,b*}` detects it. **Leaf-first
  reaches each clause only up to its deepest variable.** The mask block (bit-independent `R_i`,
  `A^{mask}_{i−1}(D_{i,0} − D_{i,1}) ≈ 0`) is never switched, and it does not need to be.
* *Meeting in the middle fails.* Root-first PL above the horizon and leaf-first below `ℓ_k` do not
  join at a level: the shift symmetry of §3 at an intermediate matrix `A^k_{ℓ_k−1}` breaks the
  dead constraint `A^k D_{ℓ_k,b*} ≈ 0`. In the projected world the `k`-pads have the form
  `(c_x E_{dead}) · D_{dead}^{-1} D_{alive}`, a short vector times a public matrix. Only the pads
  of the other alive clauses hide this.

**Changing the construction to remove the zero encodings** (send a satisfied clause into a
bit-independent "satisfied" chain instead of `0`, so that decryption stays canonical): the
satisfied chain is mask-like, and `D_{i,0} − D_{i,1}` annihilates it. The satisfying-bit targets
of the alive rows become `T A^{d}_i + E` on that mask-like block, so the zero-encoding obstruction
reappears one block over. A bit-dependent mask block with path-independent products is impossible
on the reachable subspace. Products along two paths that differ at one level must agree, so
`R_{i,0} = R_{i,1}` there. **Canonical decryption forces zero encodings of differences.**

## 6. Positive result: the cut lemma (informal proof from LWE)

**Cut lemma.** Let `L` be a level such that (i) the sub-CNF of the clauses whose variables all lie
in levels `≤ L` is already unsatisfiable, and (ii) the joint prefix rows at levels `≤ L − 1` are
linearly independent. For each bit `b`, the padded rows `((c_{x,k}·[x b falsifies k])_k)_x` at
level `L` must also be independent. Both hold generically when `2^{L−1} ≤ n'`, and in general
under a Hall-type condition with block capacity `n'`. Then the masked two-vector lemma holds from
LWE with `poly(h, width)` hops, **whatever the depth `h` and whatever the overcompleteness below
`L`**.

*Proof sketch.*

1. CVW18 phase 1 strips the CPRF block.
2. Leaf-first on the blocks of the first-`L` clauses, from level `h` down to level `L`. These
   blocks are never dead below `L`, so each step is LWE (secret `A^k_i`, public `S'_{i,0}, S'_{i,1}`)
   followed by Lemma 4.1. Their alive targets at level `L` become uniform `U_{b,k}`.
3. Root-first PL through level `L − 1`, which is allowed by (ii). `D_{L,b}` is reduced to the
   projections `w_{xb} = μ_L-part + ∑_{k ∈ F_L(xb)} c_{x,k} U_{b,k} + (other blocks) + noise`.
   Here `F_L(xb)`, the set of first-`L` clauses falsified by `xb`, is nonempty by (i), and by
   independence the pads are jointly uniform. So every projection is a fresh one-time pad.
4. `D_{L,b}` is Gaussian conditioned on uniform values, hence independent (smoothing). `A_L` is
   now used only as a preimage matrix. CVW18 Lemma 4.4, applied root-first from level `L` to the
   leaf, makes every lower `D` independent. The mask then appears only in the ciphertext.

This contains PR #49's `h = 2` and `2^{h−1} ≤ width` results (take `L = h`). It is the first proof
that covers an **overcomplete** regime: arbitrarily many twisted levels below the cut. The
smallest example is `Ψ = (x_1) ∧ (¬x_1)` followed by any number of twisted irrelevant levels.
The instances it covers are decidable in time `2^L·poly = poly(width)`, as the barrier demands.

## 7. Idea (2): induction on overcompleteness (fresh sub-blocks)

Giving one extra prefix `x*` a fresh row block at the overcomplete level is a state split. A
correlated copy is exactly the merged hybrid (`preimage_correlated_copy` of PR #49), and an
independent copy is the single-prefix split, which PR #49 §7 reduces to OPL itself. The
induction also does not terminate. A split lowers the count at one level by one, but the count
doubles at every level below, so isolation must go down a whole subtree. Keeping all levels
non-overcomplete needs about `2^h / width` copies, which is the exponential-width scheme again
(§4 costs). **Circular and exponential.**

## 8. Idea (3): switch the mask first

The mask appears in every path value. A hop that switches it while the pads are unchanged is the
masked lemma itself: it is a global change, and it is false for satisfiable `φ`. Canonical
decryption removes the SZK distinguisher of the positional split (PR #49 §7(i)). It does not
remove the hop-count requirement: the lemma is a WE statement, so any proof needs
super-polynomially many hops (`pq-we-hybrid-count-barrier`, with `stat_hops_carry` doing the
counting). §3 adds that the noiseless projections pin the mask, so a "mask first, pads later"
order has no information-theoretic slack. **Dead.**

## 9. Idea (5): attacks

* **Untwisted variant: broken whenever a short affine relation exists.** The patterns `U(z)` are
  public, being computable from `φ`. Any integer relation `∑β_z 1_{U(z)} = 0` with
  `∑β_z = s ≠ 0` and `‖β‖₁·noise < q/4` gives `∑β_z y_z = s·m + small`. CVW18's
  inclusion–exclusion (`{k}, {l}, {k,l}`, coefficients `+1, +1, −1`) is the simplest case.
  Together with §4 this pins down the untwisted scheme:
  * secure (provably, LWE) iff a degree-0 refutation exists;
  * broken if a short relation exists;
  * in between only when every relation has coefficients of size about `q/noise`.
* **Twisted candidate: no attack found.**
  * Affine relations exist but have huge coefficients (§3). Finding short ones is the
    low-rank-plus-noise lattice problem of PR #45 attack 5, a parameter condition.
  * Zeroizing rank attacks need small values. Full twisting makes all path rows distinct, so no
    difference of path values is small.
  * The mask-block leak `D_{i,0} − D_{i,1}` produces mask-free values that are still padded.
  * The zero-encoding structure of §5 (`k`-pads = short × public) is hidden behind the pads of the
    other alive clauses, and isolating one block would need path rows that differ only in block
    `k`, which twisting prevents.

## 10. Status and the exact remaining gap

* **OPL as stated is the wrong target.** In exact-row form it is vacuous at complete levels (§2).
  In any form, it leaves an end step on projections that determine the mask information-
  theoretically (§3, Lean). The masked lemma in the overcomplete regime is not "reveal only
  projections". It is "the projections' **noise** hides their exact linear relations".
* **Overcomplete cut lemma (open).** Let `L` be such that the first-`L` sub-CNF is unsatisfiable
  but `2^{L−1}` exceeds the width (one level past the horizon of §6). After steps 1–2 of §6, the
  view `(W, D_1, …, D_L)` must be indistinguishable from the one in which every level-`L` target is
  replaced by an independent uniform matrix.
  * Its padded projections are `μ R_L A^{mask}_L + ∑_k c_{x,k} U'_{b,k} + e_x D_{L,b}`, with
    `2^{L−1}` exactly dependent pads per block (level noise absorbed into `U'`). Only the
    upper-level GGH15 noise `e_x D_{L,b}` separates them from the mask.
  * It is statement-dependent: false when the first-`L` sub-CNF is satisfiable.
  * For an NP-hard family of first-`L` sub-CNFs it needs super-polynomially many hops, each
    justified by one falsified clause on one prefix.
  * The smallest open instance is `2^{L−1} = 2·width`.
  * It is not stated as a Lean node: a faithful statement needs GGH15 encodings, the coset
    Gaussian law and computational indistinguishability over all prefixes. The vocabulary for
    that is not yet in the DAG.
* **What a solution must contain.** Path-local randomness, i.e. one hop per prefix `x` past the
  horizon using `F_L(x b) ≠ ∅`, in a poly-size encoding. This is the same missing object as in
  `pq-we-evaluation-oracle-crux` (a key punctured at one witness). Within GGH15 with shared level
  secrets, no data is specific to a prefix.
* Proved in Lean (this PR): `hiding_of_separator`, `mask_of_affine_relation`,
  `separator_iff_no_affine_relation`, `affine_relation_of_span`, `untwisted_separator_iff`,
  `hop_hiding_of_point_separator`, `hop_reveal_of_span`.

## 11. The positional version (PLR hop, open PR #54) and the two-left-vector Cor. 5.9 variant

Open PR #54 (note `pq-we-masked-evaluator-mechanisms`) replaces the bit-independent mask block by
a comparator block `P_{i,b} ⊗ R_{i,b}` against a threshold `t` (states lt/eq/gt, final rows
`mask'` on lt and `mask` on eq/gt). It asks for the PLR hop `t → t+1` for a non-witness `t`,
expected to follow from "a two-left-vector version of CVW18 Cor. 5.9 restricted to a non-zero
constraint product on path `t`". The same analysis applies, and it answers that question.

* **What is better.** The eq chain of path `t` is reached by one prefix per level, so the
  comparator block is never overcomplete on it. Bit-dependent `R_{i,b}` also remove the mask-block
  zero encodings of §5. The obstruction can only come from the shared constraint block.
* **Hop dichotomy (Lean).** At the leaf, after root-first projection, the hop changes the mask of
  one path, `M_t: mask → mask'`, while every path carries the shared pad `c_z A^{con}`.
  * `hop_hiding_of_point_separator`: if `c_t ⬝ᵥ ℓ = 1` and `c_z ⬝ᵥ ℓ = 0` for `z ≠ t`
    (`c_t` outside the span of the other path rows), the flip is **perfectly hidden**.
  * `hop_reveal_of_span`: if `c_t = ∑_{z≠t} β_z c_z`, then `y_t − ∑β_z y_z` removes the pad
    exactly. It leaves `M_t − ∑β_z M_z` plus noise, where the other masks are themselves pinned
    (§3), so **the noiseless values determine the hop bit**.
* **Consequence for the requested Cor. 5.9 variant.** A two-left-vector Cor. 5.9 proved by
  CVW18's own technique (phase 1, then root-first Lemma 4.4/PL, all with hidden rows used on one
  side) ends in exactly this statistical step. It therefore holds iff `c_t ∉ span{c_z : z ≠ t}`.
  * For `2^h ≤ K n'` (generic twisting), this is the `h = 2` / small-width regime, and the variant
    and the PLR hop follow. The first test instance proposed by PR #54 (`h = 2`, two clauses) is
    covered. The cut lemma of §6 extends this to hops whose path `t` is already falsified inside
    the first `L` levels, with `2^{L−1} ≤` width.
  * For polynomial width and `2^h > K n'`, every path row is in the span of the others, so no
    such variant exists. The hop must use the GGH15 noise as LWE noise, as in §5.
* **Restricting to `M_t ≠ 0` is not enough.** It gives a non-zero pad on path `t`, but the pad is
  linearly determined by the other paths' pads, which is the overcomplete situation of §3. The
  needed statement is the computational one-path analogue of the overcomplete cut lemma: the
  noise `e_x D` hides the exact relation `c_t = ∑β_z c_z` *for one path*.
* **Is the positional hop easier than the masked lemma?** Yes, structurally. It is local (one
  path, statement-independent, falsifiable), so the hybrid-count barrier does not forbid a
  polynomial-hop proof *of the hop*. The hops are many; each individual hop may be cheap. For
  the masked lemma, by contrast, the barrier forces super-polynomially many hops. **The positional
  PLR hop is therefore the better second target.** The precise open statement is:
  > for path `t` with `M_t ≠ 0`, with the comparator isolating `t`, the views with `M_t = mask` and
  > `M_t = mask'` are indistinguishable under LWE, although `c_t` lies in the span of the other
  > path rows.

  It is an LWE statement with product secrets and GGH15 noise. The tool it needs is a
  leaf-first, BPR-type induction along path `t` only, where zero encodings stop it: at each
  variable of a clause that `t` satisfies. That is the same obstruction as in §5, now confined to
  one path.

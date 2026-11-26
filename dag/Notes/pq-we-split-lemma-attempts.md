---
title: The accept-class split lemma of the positional GGH15 WE candidate - precise statement, five lines of attack, and an SZK-type barrier against proving it by hybrids
refs: [definition:WE_CircuitSAT, note:pq-we-ggh15-chain-verdict, note:pq-we-hybrid-count-barrier, note:pq-we-gap-structure-routes, note:pq-we-evaluation-oracle-crux, note:pq-we-tree-candidate-crux, theorem:AdvancedEncryption.WE.Hybrid.stat_hops_carry, theorem:AdvancedEncryption.WE.Wee.leaf_trapdoor, theorem:AdvancedEncryption.WE.Split.preimage_congr, theorem:AdvancedEncryption.WE.Split.preimage_correlated_copy, theorem:AdvancedEncryption.WE.Split.preimage_row_transform, theorem:AdvancedEncryption.WE.Split.merged_secrets_dependent]
tags: [witness-encryption, candidate, barrier, open-problem, dead-end]
---
Design-AI sub-task (k): work on the one missing lemma of the most promising surviving candidate
for `Def_WE_CircuitSAT`. The candidate is positional GGH15 with a BGG+ leaf and the VWW-type key
`K_φ` (note `pq-we-ggh15-chain-verdict`, repaired as in its point 4). Open PR #42 (note
`pq-we-ggh15-row-partitioned-trapdoors`, not yet merged) adds trapdoors partitioned by rows, the
two hop types that are provable from LWE ((a) reroutes between reject-closed states, (b) leaf
flips of isolated paths), and a counting theorem showing that a third hop type, the
**accept-class split**, is unavoidable. This note records what was tried on the split lemma and
where each attempt stops. The main result is negative. For subtrees of super-logarithmic depth the
split lemma has **no proof with polynomially many hops** from statement-independent assumptions
(an SZK-type argument, §6). The exponential sub-walk that would be needed is circular in this
construction, because a path below the split has no fresh randomness of its own until the split
is done. Arguments are informal except the four Lean theorems in this PR, which have complete
proofs. Section 7 treats the split lemma together with the masked two-vector lemma of open
PR #45. A projection lemma, provable from LWE, proves the latter for two levels. It also shows that
both lemmas reduce to one common missing statement, an overcomplete projection lemma.

Notation is that of PR #42: levels `1..n` (`n = 128`), stacked matrices `A_i` with one row block
per state, `D_{i,b} ← A_{i−1}^{-1}(Y_{i,b})`, a fresh secret per (level, bit, source state),
comparator states eq/lt/gt, a unipotent tracker `(1, w)` on decided states, and the leaf
`[A − w⊗G | B']` with the key `K_φ ← [A_φ − G | B']^{-1}(u)`.

## 1. The statement, and the only form the walk needs

**Split lemma (general form).** A state `σ` of level `i` is in the accept class, and its incoming
transitions are `T_1 ⊔ T_2`. In `H^merge` all of them enter `σ`. In `H^split` the encoding
`A_i` gets a fresh row block `σ'` (a fresh Micciancio–Peikert sample), with fresh secrets
`S_{i+1,b,σ'}` and the same successors as `σ`, and the transitions in `T_2` enter `σ'`. Claim: for
every `φ` with no witness, `H^merge ≈_c H^split` with loss `poly(n)·ε_LWE`.

**Observation 1 (the walk only needs single-prefix splits).** In the Gray walk `H_g → H_{g'}`
(`g, g'` differ first at level `j`) the splits isolate `g'` along `g'_{≥j}`. The first one
redirects the transition `(j, g'_j)` out of `eq_{j−1}`. Every later one redirects a transition out
of the copy made by the previous split. Each of these source states is reached by **exactly one
prefix** `x*` (`eq_{j−1}` only by `g_{<j}`, each copy only by `g'_{<k}`). So `T_2` is always a
single transition carrying a single prefix `x*`. Call this case **SPS** (single-prefix split).
It is the only case the walk needs, and everything below concerns it. The paths that SPS affects
are still the `2^{n−j}` paths `x* y`. Their secrets are `u_* T_y` in `H^merge`, where `T_y` is the
product of the suffix secrets, shared with every prefix in `T_1`. In `H^split` they are
`u_* S'_{y_1} T_{y_{>1}}`.

## 2. Exact identities (Lean, complete proofs)

* `AdvancedEncryption.WE.Split.preimage_congr`: the coset Gaussian preimage law
  `Trapdoor.preimage B P τ` depends only on the cosets `{x ∈ ℤ^m : B x = P_j}`, so changing the
  stacked matrix and targets without changing these cosets leaves the law of `D` unchanged.
* `AdvancedEncryption.WE.Split.preimage_correlated_copy`: `preimage [B; RB] [P; RP] = preimage B P`.
  A correlated copy `σ' := Rσ` with targets `R Y_σ` is **exactly** `H^merge`, as PR #42 claimed.
  This is now proved for the library's preimage law.
* With `R = I` and a short `F`: the **noisy copy** `A^{(σ')} = A^{(σ)} + F` forces
  `Y_{σ'} = Y_σ + F D`, so the constraint is again implied. The `T_2` target becomes
  `P A^{(σ)} + (P F + E)`, which is `H^merge` up to noise flooding. Noisy copies can be created
  statistically along any polynomial set of paths. They do **not** give those paths fresh secrets:
  their outgoing secrets are the shared ones.
* `AdvancedEncryption.WE.Split.preimage_row_transform`: `preimage (T B) (T P) = preimage B P` for
  invertible `T` (used in §4).

So SPS is precisely "a correlated (or noisy) copy ≈ an independent copy", for one prefix.

## 3. The clear-target leak, and what remains when there is no leak

**Lemma (informal, elementary).** Let `ρ` be a state of level `k` that carries tracker rows (a
decided accept state such as gt, or a copy of one), and let `Z = (M ⊗ P) A_k^{(ρ)} + E` with `P`
short be the target of a tracker-to-tracker transition into `ρ`. Given `Z` *in the clear*
together with the published suffix `D_{k+1..n}`, one recovers `P T_y` for suffixes `y`. Hence `Z`
is far from uniform given the suffix.

*Proof.* `A_k^{(ρ)} D_y = (M_y ⊗ T_y) L + small`, where `L` is the leaf. So
`Z D_y = (M M_y ⊗ P T_y) L + small`. The tracker product is unipotent, so row `j ≥ 1` of `M M_y`
is `e_j`. Leaf row block `j` is `−G` in attribute column block `j`. That block of `Z D_y` is
therefore `−P T_y G + small`, which gadget decoding inverts (the noise is that of an honest path,
which decryption already decodes). With `Z` uniform, `Z D_y` is uniform. ∎

The general reason: one secret serves two different attributes. If small projections `λ, λ'`
of the leaf rows give `[A − w⊗G | B']` and `[A − w'⊗G | B']`, then `(λ − λ')` gives
`[(w' − w)⊗G | 0]`. Every state with fiber `≥ 2` serves at least two attributes, and the counting
theorem of PR #42 makes such accept states unavoidable. So **no basis change of the tracker** (for
instance rows `[A − e_r⊗G | B']`, each a BGG+ encoding of a binary non-witness) makes the raw
targets pseudorandom.

**No leak, but no proof either.** A *projected* target has no isolated tracker rows. Examples are
row `0` of a tracker state, an eq state, and the transition `eq_{j−1} → gt_j`, whose entry vector
is `(1, g_{<j}, b, 0, …)`. Multiplied by the suffix, such a target gives
`P T_y [A − w_y⊗G | B'] + small`, BGG+ encodings of the non-witnesses `w_y` under the product
secrets `P T_y`, for all `2^{n−k}` suffixes `y`. No leak is known. But "these are pseudorandom
given the suffix and `K_φ`" is the WE statement for the subtree, and the barrier of §6 applies to
it verbatim: with many witnesses below, decryption recovers `P T_y` exactly.

The honest adversary never sees `Z` in the clear. It sees only `u Z + small` for honest prefix
secrets `u = (1, x) ⊗ s_x` with independent `s_x`, so this is a **proof** obstruction, not an
attack (§4(5)). It has three consequences for reductions:

1. **No leaf-first step on accept rows** (this sharpens obstruction 1 of the verdict note). Every
   accept target into a tracker state is non-pseudorandom given its suffix, not only at the leaf.
   Every projected accept target is pseudorandom only if a subtree-WE statement holds.
2. **No LWE step on the `T_2` target.** The template "merged ≈ (`T_2` target uniform) ≈ split"
   needs the `T_2` target to be pseudorandom in the clear. For every split after the first one
   along `g'` (copy → gt, tracker to tracker) this is false by the lemma. For the first one (out
   of `eq_{j−1}`, projected) it is the subtree-WE statement for `x*`.
3. **Explainable targets give a trapdoor.** Without a trapdoor for `Ā^{(ρ)}` (an MP tag of `0`), a
   reduction can publish the `ρ`-rows of `D_{k+1}` only if their targets are (i) pseudorandom, or
   (ii) explainable, `Y = Ā^{(ρ)} X` with a known short `X`. For the tracker rows `j ≥ 1` of a
   tracker state `ρ`, (i) is excluded by the lemma. In case (ii),
   `Ā^{(ρ,j)} (X D_y)_{col j} = −V G + small` with `V = S_b T_y` known to the reduction, so
   `X D_y` is a gadget trapdoor for those rows, and LWE on them is decodable (obstruction 2 of the
   verdict note, now forced on the tracker rows of every tracker state). Row `0` of `ρ` escapes
   this only by falling under (i), the subtree-WE statement.

**Consequence.** A reduction that embeds an LWE challenge in the row block of one state, or in the
target of one transition, without first proving a subtree-WE statement, can do so only in
reject-closed rows or in the tracker-free eq-final leaf. Those are exactly hop types (a) and (b)
of PR #42.

## 4. The five lines of attack

**(1) Re-randomise the secrets path by path below the split** (to reach the provable
independent-secrets case). In `H^merge` the only data specific to `x*` are the `T_2` transition
and the eq chain above it. Every matrix and secret below level `j` is shared with the prefixes in
`T_1`. A hop local to one path `x* y` needs data specific to `(x*, y)` with fresh randomness. The
independent-secrets proof plants `A = BR + w⊗G` and uses LWE on that path's **fresh** secret.
Isolating `x* y` with fresh secrets means splitting along `y` below level `j`. These are again
single-prefix splits, but their sources are states that exist only after the split at level `j`.
Noisy copies (§2) give isolation without fresh secrets, which is useless: the type-(b) flip of a
noisy-copy final needs a fresh last-level secret, and the noisy copy carries the shared one.
**Stops: circular.**

**(2) CVW18 "GGH15 beyond permutation branching programs"** (Chen–Vaikuntanathan–Wee, ePrint
2018/360). Read from the full text, the proofs tolerate the following.
* **Lemma 4.1 (statistical):** `A^{-1}((z; u)) ≈_s Ā^{-1}(z)` when `u` is uniform and independent
  of `z`. This is F2 of PR #42.
* **Lemma 4.4 (computational, the important one):** for an **arbitrary** target `Z`,
  `A^{-1}(Z + E) ≈_c D_{Z,σ}` when `A` is a hidden trapdoor matrix used nowhere else. The proof is
  LWE with secret `A_1` (a column block) and public matrix `D_1`. Preimages of non-pseudorandom
  targets are fine here, but only under a matrix with no other use.
* **Theorem 5.7 / Corollary 5.9:** semantic security of `γ_{⊗diag}(M, S) = diag(M ⊗ S, S)` for
  arbitrary (even `S`-dependent) `M`, with auxiliary input the `S_{i,b}`, `J·A_0` and the top leaf
  rows `Ā_h`. Phase 1 (leaf first) removes the extra `S`-rows using LWE with secret `A̲_i` and
  public `S`. Phase 2 (root first) applies Lemma 4.4 level by level.
* **Remark 5.8:** the statement is false with `A_0` in place of `J·A_0`, because a public root
  reveals the structure of `M`.

Where it stops for the split.
* (a) Lemma 4.4 needs `A_i^{(σ)}` used only as a preimage matrix. In the candidate it is also
  the matrix of the incoming targets `P A_i^{(σ)}` (secret on the left). Using one secret matrix on
  both sides is not LWE: for public short `X, Y`, `(XA + E_1) Y − X(AY + E_2)` is small. The same
  bilinearity blocks the root, since `a_0 = s A_0 + e` and `D_1` both use `A_0`. Phase 2 avoids it
  only because `J·A_0` is masked by `A̲_0`.
* (b) A root-first induction ignores `φ`. It cannot run down to level `j` in a decryptable scheme:
  it would make the prefix encodings independent of `A_j` and break decryption for true
  statements.
* (c) **Masked-leaf variant (approach 4a).** Add CVW's `S`-rows to the candidate, with bottom
  leaf rows `A̲_h` and the decryptable effective leaf `A'' = A + A̲^{(1)}`,
  `B'' = B' + A̲^{(2)}` made public. Each path then outputs `s_w[A'' − w⊗G | B'']`, so decryption
  works. The phase-1 LWE step at the leaf is **valid** (secret `A̲`, with `A := A'' − A̲`
  implicit). Afterwards, on every accept row the targets are `(K − (m_b⊗I)U ; U)`, with `K` the
  unmasked targets on the public leaf. The row transform `[[I, m_b⊗I], [0, I]]` turns them into
  `(K ; U)` (`preimage_row_transform`), and Lemma 4.1 then gives a preimage of `K` under
  `Ā + (m_b⊗I)A̲`, a fresh uniform matrix. **The masked scheme is the unmasked scheme again.** The
  mask cannot survive on accept rows, because a witness must be able to remove it.

**Stops:** CVW18 handles non-pseudorandom targets only under matrices with no other use, which in
a decryptable GGH15 never holds on accept rows.

**(3) Micciancio–Peikert tags / ABB puncturing.** With `A^{(σ)} = [Ā | ĀR + hG]`, the tag copies
`h ≠ h'` are themselves correlated copies. ABB works because the punctured identity never needs a
key. Here the copy `σ'` needs outgoing preimages. With tag `0` these exist only for explainable
targets, which give a trapdoor by §3.3. **Stops: trapdoor propagation.**

**(4) Change the construction** (width, copies, randomisation layers).
* *Masking rows:* collapses, see (2c).
* *Independent secrets per tracker row:* the final row blocks then carry different secrets, and
  `Σ_r v_r L_r` is no longer a BGG+ encoding under one secret. **Breaks decryption.**
* *Tracker basis change* to binary attributes `0, e_r` (all non-witnesses when `φ` is false):
  the generic form of §3 still applies (one secret, two attributes). **Dead.**
* *State copies made at encryption time* (`K` copies, pseudorandom routing): a final state is
  still shared by `2^n / K` accepted paths, so the counting theorem is unchanged. **Dead.**
* *"Untrack" one coordinate* (set `U_{k,1} := I`, so that every path's attribute loses `w_k`):
  all attributes are non-witnesses, so this is semantically free. But `n` such hops followed by
  the leaf lemma at attribute `0` (`A = BR`, `K_φ` simulated by the `−G` trapdoor of
  `AdvancedEncryption.WE.Wee.leaf_trapdoor`) and a leaf-first induction would be a
  **polynomial-hop** proof. That contradicts `pq-we-hybrid-count-barrier`, so each untrack hop is
  as hard as WE itself. This is a useful sanity check: any hop that changes shared data for
  exponentially many paths inherits the barrier, which is §6.

**(5) Attacks on the candidate.** None found. The leaks of §3 need a target in the clear, and the
adversary sees targets only through honest projections `u Z` with independent prefix secrets.
Combining two prefixes gives a rank-two tracker tensor, not an isolated row. Path secrets of
distinct prefixes differ at the first differing level, so there are no exact relations.
`K_φ` gives no zero test on non-witnesses. The low-rank test (prefix encodings into `σ` lie near a
`d_σ`-dimensional space) is a lattice problem of dimension about `d_σ log q / log β`, so it is a
parameter constraint, as PR #42 says. The real ciphertext remains unbroken. Note that the split
lemma is **false** for statements with enough structured witnesses:
`AdvancedEncryption.WE.Split.merged_secrets_dependent` (Lean) says that `d + 1` merged secrets
`u_x T` are linearly dependent, and decryption returns them exactly. In `H^split` the row of `x*`
uses a fresh factor and is generically independent.

## 5. Where the honest adversary and the reduction differ

The honest adversary sees each accept target only through `u·Z` for honest prefixes `u`. Every
known reduction template needs the target in the clear or explainable. A proof of SPS would have
to keep `Z` hidden throughout, for example by an argument about the joint law of `(c_{x*}, D_j)`
in which the only correlation is `c_{x*} D_j ≈ u_* Z`. No LWE technique of this kind is known.
The natural candidate statement is: given `c = uA + e` and `D ← A^{-1}(Z)` with `A` hidden, the
view depends on `Z` only through `uZ + small`. That is itself a one-row form of evasive LWE.

## 6. SZK-type barrier for the split lemma itself

Fix a level `j` such that `n − j` is super-logarithmic and `gt_j` is entered by at least
`d = n_LWE` prefixes of `T_1` (true once `2^j ≫ d`, so for all but the first `≈ log₂ d` levels).
Let `Π_YES` be the statements with witnesses `x y` for `d` prefixes `x ∈ T_1` and for `x*`, and
for suffixes `y` of both first bits. Let `Π_NO` be the unsatisfiable statements. The pair
`(Π_YES, Π_NO)` is NP-hard: for a CNF `ψ` on `k` variables take `φ(x, y) := ψ(y_{2..k+1})`. On
`Π_YES`, decryption returns the path secrets `s_{xy}` exactly. In `H^merge`, `s_{xy} = s_x T_y`
with `s_x ∈ Z_q^d`, so the `d + 1` concatenated rows `(s_{x y_1}, …, s_{x y_K})` factor through
`[T_{y_1} | … | T_{y_K}]` and are linearly dependent
(`AdvancedEncryption.WE.Split.merged_secrets_dependent`). In `H^split` the row of `x*` factors
through `[S'_0 T_a | S'_1 T_b]`. It lies in the span only if `s_* S'_0 S_0^{-1} S_1 = s_* S'_1`,
which fails generically. This is why suffixes of both first bits are needed: with one first bit
`b`, the two row spaces coincide. So the decryptor distinguishes `H^merge` from `H^split` with
advantage close to `1`. Suppose SPS at level `j` had a proof with `T = poly` hops, each either
statistical on `Π_NO` or computational under a statement-independent assumption (valid on
`Π_YES` too). By `AdvancedEncryption.WE.Hybrid.stat_hops_carry`, the statistical hops then carry
distance `≥ 1 − negl` on `Π_YES` and `negl` on `Π_NO`. Sahai–Vadhan polarisation puts
`(Π_YES, Π_NO)` in SZK, and the polynomial hierarchy collapses, as in
`pq-we-hybrid-count-barrier`. **So the split at level `j` needs super-polynomially many hops in `n − j`**
(heuristically one per path `x* y`, about `2^{n−j}`), each justified by a local fact
`φ(x* y) = 0`.

The hop budget is not the problem: the walk does `2^{j−1}` splits at level `j`, so
`Σ_j 2^{j−1} · 2^{n−j+1} ≈ n · 2^n`. The problem is that such a sub-walk needs a local hop for
each path `x* y`, and §4(1) shows that in `H^merge` no data below level `j` is specific to
`(x*, y)`. Fresh path-specific randomness appears only after the split. Within this construction,
then, the split lemma is not just unproved. **It cannot be proved by a hybrid argument of the
allowed kind, either directly (§6, polynomially many hops) or by a sub-walk (circular).** The
only splits outside the barrier are those near the leaf (`n − j = O(log λ)`), where a constant
or polynomial number of non-local hops is not excluded. They are still blocked by §3, which leaves
no place to embed LWE.

**The top levels are different, and the difference is suggestive.** If fewer than `d` prefixes
share `σ` (`|T_1| < d`, the first `≈ log₂ d` levels), the vectors `s_x` (`x ∈ T_1 ∪ {x*}`) are
generically independent. For uniform `S_b` the tuple `(s_x S_b)_x` is then uniform, so
`s_* S_b` is independent of the other prefixes' secrets, exactly as `s_* S'_b` is. Merged and
split agree at the level of the secrets, and no witness-based distinguisher exists. A proof
would still have to handle the short (Gaussian) secrets and the encodings, so this is only a hint.
It does not help the walk, which needs splits at every level along `g'`.

## 7. Joint view with the masked two-vector lemma (open PR #45), and a projection lemma

Open PR #45 (note `pq-we-witness-prf-masked-evaluator`, not yet merged) reaches the same difficulty
from a masked γ⊗-GGH15 WE. That scheme follows CVW18 Construction 10.1 with secrets
`diag(R_i, M_{i,b} ⊗ S'_{i,b}, S_{i,b})`, a bit-independent mask block `R_i`, and two left
vectors whose difference is the public row combination `W = A_0^{mask,e} − j_C A_0^{con}`.
Treating the two lemmas together gives the following.

**(i) Canonical decryption defeats the §6 distinguisher.** The §6 barrier needs decryption on YES
instances to return path-dependent data, namely the exact secrets `s_{xy}`, whose rank exposes
`H^merge`. In the masked scheme every witness decrypts to the same mask. Hops that change only
constraint-block data are therefore invisible to the decryptor, and §6 does not rule out local
hops there. This is a genuine structural advantage of the masked candidate. The positional
candidate could adopt it only by changing what decryption returns.

**(ii) The mask block has its own clear-target leak.** `R_{i+1}` does not depend on the bit, so
`Δ = D_{i+1,0} − D_{i+1,1}` satisfies `A_i^{mask} Δ = small`. Any clear mask target
`R_i A_i^{mask} + E` then has `(R_i A_i^{mask} + E) Δ` small. So no LWE step may switch a
mask-block target at a level `< h`, the same obstruction as §3.

**(iii) Projection lemma (PL), provable from LWE.** Let `A = T^{-1}[P; H]` with `T` invertible,
where the rows `P` are known to the reduction and `H` is uniform, hidden, and used **only** as
rows of the preimage matrix of `D_1, …, D_t ← A^{-1}(Y_j + E_j)` (targets arbitrary, noise `E_j`).
Then `{D_j}` is computationally close to Gaussians conditioned only on `P D_j = (T(Y_j + E_j))_P`.
*Proof.* Apply `preimage_row_transform`, then Bonsai (`H = [H' | H'']`, `D = [D'; D'']`), with
`[P''; H'']` sampled jointly with a trapdoor. LWE with secret `H'` (rows) and public
`[D'_1 | … | D'_t]` replaces `H' D'_j + noise` by uniform values. CVW18 Lemma 4.1 then drops the
`H` rows. This is CVW18's Lemma 4.4 with public rows allowed; it needs `H` to be used on one side
only. In words: **the preimages reveal only the projections `P D_j`**.

**(iv) Consequence: a proof of the masked lemma for `h = 2` (every CNF), and more generally
whenever `2^{h−1} ≤` the number of rows of each `A_i`.**
* CVW18 phase 1 (leaf first) strips the CPRF rows `A_i^{bot}` at every level, after which
  `u_C` is uniform and `u_O = u_C + W`.
* PL at the root (`P = W`, the remaining rows hidden) reduces `D_{1,a}` to its projections
  `w_a = W D_{1,a}`.
* At level 1, take as `P` the rows `X_a A_1` with `X_a = (r_0 R_1 | −(j ⊙ alive_a) ⊗ p_a)` (known
  to the reduction). If `X_0, X_1` are linearly independent, the rest of `A_1` is hidden and is
  used only as preimage rows, so PL reduces `D_{2,b}` to the projections `w_{a,b}`. These are
  `mask − Σ_{k unsat by (a,b)} j_k p_a S'_{2,b} A_2^{con,k} + small`.
* The leaf matrices `A_2^{con,k}` are used on one side only, so LWE turns every pad of an
  unsatisfied path into a uniform value. Unsatisfiability gives a pad on every path. The mask
  `r_0 R_* A_2^{mask}` then appears only in the ciphertext and is uniform.

For depth `h` the same induction needs the `2^i` prefix rows `X_x A_i` at level `i` to be
linearly independent, so `2^i ≤ rows(A_i)`, i.e. width exponential in `h`. That is consistent
with the barriers, and the hop count is polynomial in the width. The positional split behaves in
exactly the same way. When at most `rows` prefix rows enter each state below `σ` (the
`|T_1| < d` regime of §6), PL makes `{X_x A}` jointly uniform whatever the correlation among the
`X_x`, so merged and split coincide. Both lemmas fail exactly where the prefix rows become
**overcomplete**.

**(v) The common missing lemma: overcomplete projection.** When `N > rows(A)` prefix rows
`w_x = X_x A + e_x` (with `X_x` products of GGH15 secrets) enter a level, `A` has no hidden part
used on one side only. The needed statement is: preimages `D ← A^{-1}(Y)` reveal only the
projections `{w_x D}`. This is an evasive-LWE-type statement (CVW18 Remark 5.8 is its failure for
a single public `A_0`). For the positional candidate it is moreover false on YES instances (§6);
for the masked candidate (i) leaves room. **The masked candidate is the better host for further
work**, and the first open instance is `h` with `2^{h−1} = rows + 1`: one level that is
overcomplete by a single prefix row.

## Verdict and remaining gap

* Proved (Lean, complete): `preimage_congr`, `preimage_correlated_copy` (correlated copy =
  merged), `preimage_row_transform`, `merged_secrets_dependent`.
* Reduced: the walk needs only single-prefix splits (§1).
* Barriers:
  * the clear-target leak excludes LWE embeddings in the tracker rows of every tracker state
    and in the `T_2` targets of all but the first split. The remaining projected targets need a
    subtree-WE statement, to which §6 applies (§3);
  * CVW18's tolerance of arbitrary targets needs unused matrices, which never holds on accept
    rows, and masking collapses by a row transform (§4(2));
  * MP or ABB puncturing fails by trapdoor propagation (§4(3));
  * the SZK argument rules out a polynomial-hop proof of a split with a large subtree, and the
    exponential sub-walk is circular (§6).
* No attack on the real candidate was found; the split lemma is false for many-witness
  statements (§4(5)).
* With PR #45: canonical decryption escapes the §6 distinguisher; a provable projection
  lemma gives the masked lemma for `h = 2` and whenever the prefix rows are not overcomplete
  (§7).
* **Remaining gap.** The overcomplete projection lemma (§7(v)), common to both candidates.
  For the positional candidate, escaping also requires a construction in which every candidate path `x* y`
  carries randomness of its own *before* any split. With polynomial size that randomness must be
  pseudorandom and **punctured at a path** in the hybrid. That is the punctured-programming
  object of `pq-we-evaluation-oracle-crux` and `pq-we-tree-candidate-crux` (a homomorphically
  evaluated PRF whose key is punctured at one witness), not a GGH15 lemma. For the positional
  GGH15 candidate the lead closes.
